package fuse

import (
	"container/list"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"github.com/hanwen/go-fuse/v2/fuse"
	"github.com/juicedata/juicefs/pkg/meta"
	"github.com/juicedata/juicefs/pkg/utils"
	"github.com/juicedata/juicefs/pkg/vfs"
	"io"
	"math"
	"net/http"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"
	"syscall"
	"time"
)

const MaxReadTimeLength = 30
const CheckBusyTime = 300 //检查IO Busy的周期
const PruneTime = 300     //检查剪枝的时间
const LeastLengthToJudge = 20
const TuneTime = 60

// 以字节为单位: * 1024 = KB; * 1024 * 1024 = MB; 1024 * 1024 * 1024 = GB
const EntrySize = 4 * 1024
const ReuseWindowSize = 128 * 1024 * 1024 //重用窗口大小
const StrideSize = 64 * 1024 * 1024
const MinCacheSize = 64 * 1024 * 1024
const CapacityToTune = 512 * 1024 * 1024      //一次调整的缓存大小
const InitialCapacity = 256 * 1024 * 1024     //初始缓存单元大小
const MaxCacheSize = 100 * 1024 * 1024 * 1024 //最大缓存大小，应该根据实际情况调整

const stagingDir = "rawstaging"

const cacheDir = "raw"

var (
	// 使用sync.Map来安全地存储和管理待删除的文件路径
	pendingDeletions sync.Map
)

type Pair struct {
	First  float64
	Second float64
}

type Access struct {
	name   interface{} //可能是各种类型
	tBegin int64
	tEnd   int64
}

func min(a, b uint64) uint64 {
	if a < b {
		return a
	}
	return b
}

func absDiff(a, b uint32) uint32 {
	if a > b {
		return a - b
	}
	return b - a
}

// StreamNode 表示文件树中的一个节点。
type StreamNode struct {
	// filePathName string
	pathName      string
	father        *StreamNode
	childList     []*StreamNode
	inode         uint64            //对应的Inode
	isFile        bool              //是一个文件节点
	isDir         bool              //是一个文件夹节点
	cTime         int64             //节点被create的时间
	accessWindow  []Access          // 对下一层的观察，目录观察目录，目录观察文件，文件观察文件块
	readTime      []int64           //对于节点设定的read时间列表，为了计算busy时间，向上传递
	noDict        map[string]uint32 //下层自编号map：string-->uint32，字典序排序
	noLower       uint64            // 下一层，目录、文件、文件块数量
	cacheUnitNode *StreamNode       //每个节点对应的cacheUnit节点，向上收束

	accMu       sync.RWMutex // accessWindow的锁
	readMu      sync.RWMutex // readTime的锁
	noMu        sync.RWMutex // noDict的锁
	childListMu sync.RWMutex // 增加对childList的锁控制，不然可能并发导致同一节点被创建两次

	blocks []chunkObj //针对一个文件节点的信息
	size   uint64     //对文件记录大小，为了在CacheUnit中估计MaxSize中使用（目录记为0）
}

func NewStreamNode(p string, i uint64, f *StreamNode) *StreamNode {
	return &StreamNode{
		pathName:      p + "/",
		father:        f,
		childList:     make([]*StreamNode, 0),
		inode:         i,
		size:          0,  //对文件记录大小，为了在CacheUnit中估计MaxSize中使用（目录记为0）
		cTime:         -1, //最后一次被Lookup的时间
		accessWindow:  make([]Access, 0),
		isFile:        false, //	默认是false，如果被open认为是文件
		isDir:         true,  // 也可以通过OpenDir来判断目录
		readTime:      make([]int64, 0),
		noDict:        nil, //此处不初始化，为了配合后续判断不做重复操作
		noLower:       0,
		cacheUnitNode: nil,
	}
}

// StreamTree 用于管理文件影子树
type StreamTree struct {
	root             *StreamNode
	fs               *fileSystem
	nodeNum          int
	accessNum        int
	unitNodeList     []*StreamNode
	freeCapacity     uint64
	newCacheUnitSize int
	accessToTune     int                    // 调整的轮数
	m                map[uint64]*StreamNode // Ino和*FileShadowNode的映射关系
	isDatasetBusy    map[string]float64
	totalCacheSize   uint64 //总缓存大小

	uuid       string
	cacheDir   string
	mountPoint string

	nodeUnitDict map[*StreamNode]*CacheUnit //为每一个节点找到CacheUnit
	unitList     []*CacheUnit
	mu           sync.RWMutex //nodeUnitDic和unitList
	inoMu        sync.RWMutex //ino映射关系，即m的锁

	inodeLocks   map[uint64]*sync.Mutex // 不允许并发进程对同一个inode进行ProcessOpen或ProcessRead
	inodeLocksMu sync.RWMutex           // 用于保护inodeLocks映射的
}

func NewStreamTree(fs *fileSystem) *StreamTree {
	tree := &StreamTree{
		root:             NewStreamNode("", 1, nil), // 初始化 root 节点
		fs:               fs,
		nodeNum:          1, //根节点
		unitNodeList:     make([]*StreamNode, 0),
		newCacheUnitSize: 512,
		accessToTune:     200,
		m:                make(map[uint64]*StreamNode),
		isDatasetBusy:    make(map[string]float64),
		nodeUnitDict:     make(map[*StreamNode]*CacheUnit),
		unitList:         make([]*CacheUnit, 0),

		inodeLocks: make(map[uint64]*sync.Mutex),
	}
	tree.inoMu.Lock()
	tree.m[1] = tree.root
	tree.inoMu.Unlock()
	tree.mountPoint = tree.fs.conf.Meta.MountPoint
	tree.cacheDir = tree.fs.conf.Chunk.CacheDir
	tree.totalCacheSize = tree.fs.conf.Chunk.CacheSize
	tree.freeCapacity = tree.totalCacheSize
	tree.uuid = tree.fs.conf.Format.UUID
	tree.GenerateNoDictAndJudgeUnit(1) //生成根目录的NoDict
	tree.printTreeStatus()
	// go tree.CalIOBusyTime()
	//go tree.Prune()
	// go tree.DispatchServer()
	go tree.doTraverse()
	go tree.ProcessCacheUnit() // 处理CacheUnit
	return tree
}

// printTreeStatus 打印树的基本状态
func (t *StreamTree) printTreeStatus() {
	fmt.Println("StreamTree Status: \n",
		"MountPoint: ", t.mountPoint, "\n",
		"UUID: ", t.uuid, "\n",
		"CacheDir: ", t.cacheDir, "\n",
		"TotalCacheSize: ", t.totalCacheSize)

}

func (t *StreamTree) doTraverse() {
	for {
		time.Sleep(time.Second * 20)
		fmt.Println("-----------------------------")
		go t.TraverseTree(t.root, 0)

	}
}

// TraverseTree 调试是否能够正常建立树形结构
func (t *StreamTree) TraverseTree(node *StreamNode, depth int) {
	if node == nil {
		return
	}

	// 打印节点信息，depth 表示节点的深度
	fmt.Printf("%sNode: %s, Inode: %d\n", getIndent(depth), node.pathName, node.inode)

	// 递归遍历子节点
	for _, child := range node.childList {
		t.TraverseTree(child, depth+1)
	}
}

// getIndent 辅助函数，用于在打印时增加缩进，使树的结构更清晰
func getIndent(depth int) string {
	indent := ""
	for i := 0; i < depth; i++ {
		indent += "  "
	}
	return indent
}

func openController(dpath string) (*os.File, error) {
	st, err := os.Stat(dpath)
	if err != nil {
		return nil, err
	}
	if !st.IsDir() {
		dpath = filepath.Dir(dpath)
	}

	fp, err := os.OpenFile(filepath.Join(dpath, ".control"), os.O_RDWR, 0)

	return fp, err
}

func readControl(cf *os.File, resp []byte) int {
	for {
		if n, err := cf.Read(resp); err == nil {
			return n
		} else if err == io.EOF {
			// time.Sleep(time.Millisecond * 300)
		} else if errors.Is(err, syscall.EBADF) {
			logger.Fatalf("JuiceFS client was restarted")
		} else {
			logger.Fatalf("Read message: %d %s", n, err)
		}
	}
}

func readProgress(cf *os.File, showProgress func(uint64, uint64)) (data []byte, errno syscall.Errno) {
	var resp = make([]byte, 2<<16)
END:
	for {
		n := readControl(cf, resp)
		for off := 0; off < n; {
			if off+1 == n {
				errno = syscall.Errno(resp[off])
				break END
			} else if off+17 <= n && resp[off] == meta.CPROGRESS {
				//showProgress(binary.BigEndian.Uint64(resp[off+1:off+9]), binary.BigEndian.Uint64(resp[off+9:off+17]))
				off += 17
			} else if off+5 < n && resp[off] == meta.CDATA {
				size := binary.BigEndian.Uint32(resp[off+1 : off+5])
				data = resp[off+5:]
				if size > uint32(len(resp[off+5:])) {
					tailData, err := io.ReadAll(cf)
					if err != nil {
						logger.Errorf("Read data error: %v", err)
						break END
					}
					data = append(data, tailData...)
				} else {
					data = data[:size]
				}
				break END
			} else {
				logger.Errorf("Bad response off %d n %d: %v", off, n, resp)
				break
			}
		}
	}
	if errno != 0 && runtime.GOOS == "windows" {
		errno += 0x20000000
	}

	return
}

type chunkObj struct {
	ChunkIndex     uint64
	Key            string
	Size, Off, Len uint32
}

// GetInfoByInode 由一个块读取块信息
func GetInfoByInode(i uint64) ([]chunkObj, string, uint64, error) {
	inode := i
	//d, err := os.Getwd()
	//if err != nil {
	//	logger.Errorf("Get working directory error: %s", err)
	//	return err
	//}

	d := "/mnt/jfs" //TODO：从系统中获得根路径
	//d := t.fs.conf.Meta.MountPoint

	f, err := openController(d)
	if err != nil {
		logger.Errorf("Open control file for %s: %s", d, err)
		return nil, "", 0, err
	}
	defer f.Close()

	// fmt.Println("reach 1")

	wb := utils.NewBuffer(8 + 11)
	wb.Put32(meta.InfoV2)
	wb.Put32(11)
	wb.Put64(inode)
	wb.Put8(0) // recursive
	wb.Put8(0) // raw
	wb.Put8(0) // strict
	_, err = f.Write(wb.Bytes())
	if err != nil {
		logger.Fatalf("write message: %s", err)
		return nil, "", 0, err
	}

	// fmt.Println("reach 2")

	data, errno := readProgress(f, func(count, size uint64) {})
	if errno != 0 {
		logger.Errorf("failed to get info: %s", syscall.Errno(errno))
		return nil, "", 0, errno
	}

	// fmt.Println("reach 3")

	var resp vfs.InfoResponse
	err = json.Unmarshal(data, &resp)
	if err != nil {
		logger.Errorf("json unmarshal error: %s", err)
		return nil, "", 0, err
	}

	//if len(resp.Objects) > 0 {
	//	fmt.Println("Objects info for inode", inode, ":")
	//	for _, o := range resp.Objects {
	//		fmt.Printf("  ChunkIndex: %d, ObjectName: %s, Size: %d, Offset: %d, Length: %d\n",
	//			o.ChunkIndex, o.Key, o.Size, o.Off, o.Len)
	//	}
	//} else {
	//	fmt.Println("No objects found for inode", inode)
	//}

	var chunks []chunkObj
	for _, obj := range resp.Objects {
		chunks = append(chunks, chunkObj{
			ChunkIndex: obj.ChunkIndex,
			Key:        obj.Key,
			Size:       obj.Size,
			Off:        obj.Off,
			Len:        obj.Len,
		})
	}
	if len(resp.Paths) == 0 {
		err := errors.New("can't find path")
		logger.Errorf("error: %s", err)
		return nil, "", 0, err
	}
	// fmt.Println(resp.Paths[0])
	return chunks, resp.Paths[0], resp.Summary.Size, nil

}

func recursiveGetSizeByInode(inode uint64) (uint64, uint64, error) {
	// 获取当前目录的绝对路径（这里假设当前目录是文件系统的挂载点）
	d := "/mnt/jfs"

	// 打开控制文件
	f, err := openController(d)
	if err != nil {
		logger.Errorf("Open control file for %s: %s", d, err)
		return 0, 0, err
	}
	defer f.Close()

	// 准备发送的消息
	wb := utils.NewBuffer(8 + 11)
	wb.Put32(meta.InfoV2) // 命令版本
	wb.Put32(11)          // 消息长度
	wb.Put64(inode)       // inode编号
	wb.Put8(uint8(1))     // 递归标志
	wb.Put8(0)            // raw 标志
	wb.Put8(0)            // strict 标志

	// 写入请求数据
	_, err = f.Write(wb.Bytes())
	if err != nil {
		logger.Fatalf("write message: %s", err)
		return 0, 0, err
	}

	// 读取响应数据
	data, errno := readProgress(f, func(count, size uint64) {
		// 这里可以根据需要处理进度更新
	})
	if errno != 0 {
		logger.Errorf("failed to get info: %s", syscall.Errno(errno))
		return 0, 0, syscall.Errno(errno)
	}

	// 解析响应
	var resp vfs.InfoResponse
	err = json.Unmarshal(data, &resp)
	if err != nil {
		logger.Errorf("json unmarshal error: %s", err)
		return 0, 0, err
	}

	// 输出获取的信息
	//fmt.Println("Information retrieved:")
	//fmt.Printf("  inode: %d\n", resp.Ino)
	//fmt.Printf("  files: %d\n", resp.Summary.Files)
	//fmt.Printf("   dirs: %d\n", resp.Summary.Dirs)
	//fmt.Printf(" length: %s\n", utils.FormatBytes(resp.Summary.Length))
	//fmt.Printf("   size: %s\n", utils.FormatBytes(resp.Summary.Size))
	return resp.Summary.Files, resp.Summary.Size, nil
}

func (t *StreamTree) FindInodeByLookup(ino uint64, name string) uint64 {
	lin := new(fuse.InHeader)
	lout := new(fuse.EntryOut)
	lin.Pid = uint32(os.Getpid())
	lin.Gid = uint32(os.Getgid())
	lin.Uid = uint32(os.Getuid())

	lin.NodeId = ino
	fakeOneCancel := make(chan struct{})
	defer close(fakeOneCancel)
	t.fs.Lookup(fakeOneCancel, lin, name, lout)
	return lout.NodeId
}

// ReadDirNames 可以列出一个文件夹下的所有文件，用于编号
func (t *StreamTree) ReadDirNames(i uint64) []string {
	oin := new(fuse.OpenIn)
	oout := new(fuse.OpenOut)
	oin.Pid = uint32(os.Getpid())
	oin.Gid = uint32(os.Getgid())
	oin.Uid = uint32(os.Getuid())

	oin.NodeId = i
	fakeOneCancel := make(chan struct{})
	defer close(fakeOneCancel)
	_ = t.fs.OpenDirForNames(fakeOneCancel, oin, oout)
	fh := oout.Fh

	rin := new(fuse.ReadIn)
	rin.Pid = uint32(os.Getpid())
	rin.Gid = uint32(os.Getgid())
	rin.Uid = uint32(os.Getuid())
	rin.NodeId = i
	rin.Fh = fh
	fakeTwoCancel := make(chan struct{})
	defer close(fakeTwoCancel)
	rst, _ := t.fs.ReadDirNames(fakeTwoCancel, rin)
	return rst
}

// GenerateNoDictAndJudgeUnit 生成自编号词典和判断是否是CacheUnit
func (t *StreamTree) GenerateNoDictAndJudgeUnit(i uint64) {
	// 生成CacheUnit
	// 该节点的父母不存在
	t.inoMu.RLock()
	node, exists := t.m[i]
	t.inoMu.RUnlock()
	if !exists {
		return
	}

	names := t.ReadDirNames(i)

	// 目录下数量, 剪去.和..
	node.noLower = uint64(len(names)) - 2

	if names == nil {
		return
	}
	var filteredNames []string
	for _, name := range names {
		if name != "." && name != ".." {
			filteredNames = append(filteredNames, name)
		}
	}
	names = filteredNames

	sort.Strings(names)

	// 初始化自编号
	// 再次判断处理并发
	//if node.noDict == nil {
	//	node.noMu.Lock()
	//	node.noDict = make(map[string]uint32)
	//	for i, s := range names {
	//		node.noDict[s] = uint32(i)
	//	}
	//	node.noMu.Unlock()
	//}

	// 编号
	node.noDict = make(map[string]uint32)
	for i, s := range names {
		node.noDict[s] = uint32(i)
	}

	if node.father == nil {
		return
	}
	// 判断CacheUnit
	// 如果父节点已经是cacheUnitNode, 则继承父点的cacheUnitNode
	if node.father.cacheUnitNode != nil {
		node.cacheUnitNode = node.father.cacheUnitNode
		return
	}

	// 特殊判断，基于观察
	if node.pathName == "train/" || node.pathName == "val/" || node.pathName == "test/" {
		node.cacheUnitNode = node
		u := NewCacheUnit(node, t)
		go u.GetFileNumsAndSize()
		t.mu.Lock()
		t.nodeUnitDict[node] = u
		t.unitList = append(t.unitList, u)
		t.mu.Unlock()
		return
	}

	prefixCount := make(map[string]int)
	for _, name := range names {
		if len(name) >= 3 {
			prefix := name[:3]
			prefixCount[prefix]++
		}
	}

	halfLength := len(names) / 2
	for _, count := range prefixCount {
		if count > halfLength {
			// 一个新的CacheUnit
			node.cacheUnitNode = node
			u := NewCacheUnit(node, t)
			go u.GetFileNumsAndSize()
			t.mu.Lock()
			t.nodeUnitDict[node] = u
			t.unitList = append(t.unitList, u)
			t.mu.Unlock()
		}
	}

	//// 边界条件判断，说明已经到了文件
	//if names == nil && node.cacheUnitNode == nil {
	//	node.cacheUnitNode = node
	//	u := NewCacheUnit(node, t)
	//	go u.GetFileNumsAndSize()
	//	t.nodeUnitDict[node] = u
	//	t.unitList = append(t.unitList, u)
	//}
}

// Deprecated: Use NewFunction instead.
// ProcessLookup 可能在元数据缓存存在时缺失部分Lookup导致建树失败，所以同一使用 ProcessOpen 来建树
func (t *StreamTree) ProcessLookup(ip uint64, ic uint64, name string, time int64) {
	//t.mu.Lock()
	//defer t.mu.Unlock()
	//_, exists := t.m[ic]
	//if exists {
	//	t.m[ic].cTime = time
	//	return
	//}
	//
	//// 该节点的父母不存在
	//parent, exists := t.m[ip]
	//if !exists {
	//	return
	//}
	//
	//// 建立父节点和子节点关系
	//node := NewStreamNode(name, ic, parent)
	//t.nodeNum += 1
	//node.isDir = true // 默认为目录节点
	//parent.childList = append(t.m[ip].childList, node)
	//t.m[ic] = node
	//
	//// 对目录下文件进行编号
	//t.GenerateNoDictAndJudgeUnit(ip)
	//
	//// 将文件的访问记录添加到目录下
	//// node.accessWindow = append(node.accessWindow, name)
	//
	//length := len(node.accessWindow)
	//if length == 0 {
	//	a := Access{name, time, time}
	//	node.accessWindow = append(node.accessWindow, a)
	//} else {
	//	last := node.accessWindow[length-1]
	//	if name == last.name {
	//		last.tEnd = time
	//	} else {
	//		a := Access{name, time, time}
	//		node.accessWindow = append(node.accessWindow, a)
	//	}
	//
	//}
	//
	////// 调试树结构的生成
	////if t.nodeNum%50 == 0 {
	////	t.TraverseTree(t.root, 0)
	////}
}

func (node *StreamNode) AddAccess(name interface{}, time int64) {
	length := len(node.accessWindow)
	if length == 0 {
		a := Access{name, time, time}
		node.accMu.Lock()
		node.accessWindow = append(node.accessWindow, a)
		node.accMu.Unlock()
	} else {
		node.accMu.RLock()
		last := node.accessWindow[length-1]
		node.accMu.RUnlock()
		if name == last.name {
			last.tEnd = time
		} else {
			a := Access{name, time, time}
			node.accMu.Lock()
			node.accessWindow = append(node.accessWindow, a)
			node.accMu.Unlock()
		}
	}

	if len(node.accessWindow) > 50 {
		node.accMu.Lock()
		node.accessWindow = node.accessWindow[len(node.accessWindow)-50:]
		node.accMu.Unlock()
	}

}

func (t *StreamTree) doPrefetch(node *StreamNode) {
	// 从上向下判断，各层级的预取，目录、文件、文件块

}

func (t *StreamTree) ProcessOpenTest(i uint64, timet int64) {
	blocks, path, _, err := GetInfoByInode(5)
	if err != nil {
		fmt.Println(err)
	}
	fmt.Println(blocks)
	fmt.Println(path)

	fmt.Println(time.Now().Format("2006/01/02 15:04:05"), "ProcessOpenTest finish: ", i)

}

func (t *StreamTree) ProcessRead1(i uint64, off uint64, size uint32, timet int64) {
	// 同一个文件节点，串行处理
	t.inodeLocksMu.Lock()
	mutex, exists := t.inodeLocks[i]
	if !exists {
		mutex = &sync.Mutex{}
		t.inodeLocks[i] = mutex
	}
	t.inodeLocksMu.Unlock()

	var node *StreamNode

	t.inoMu.RLock()
	n, exists := t.m[i]
	t.inoMu.RUnlock()
	if exists {
		node = n
	} else {
		node = t.buildTree(i, timet)
	}

	// 记录IO_bound功能，从当前节点开始，向上遍历所有父节点
	for nn := node; nn != nil; nn = nn.father {
		// 更新当前节点的readTime
		nn.readMu.Lock()
		nn.readTime = append(nn.readTime, timet)
		// 如果readTime长度超过最大值，则移除最早的元素
		if len(nn.readTime) > MaxReadTimeLength {
			nn.readTime = nn.readTime[1:] // 移除第一个元素
		}
		nn.readMu.Unlock()
	}

	//fmt.Println(i, ": reach4")

	var accumulatedOffset uint64 = 0
	var readEnd uint64 = off + uint64(size)

	blocks := node.blocks

	for j, block := range blocks {
		if accumulatedOffset+uint64(block.Len) > off && accumulatedOffset < readEnd {
			// 记录块号
			// 加入观察窗口
			node.AddAccess(uint32(j), timet)
			//fmt.Println("block add1: ", j)
			t.mu.RLock()
			u, e := t.nodeUnitDict[node.cacheUnitNode]
			t.mu.RUnlock()
			if e {
				u.AddItem(CacheItem{block.Key, block.Size})
			}
			//fmt.Println("block add2: ", j)
		}
		accumulatedOffset += uint64(block.Len)
		if accumulatedOffset >= readEnd {
			break
		}
	}

	fmt.Println(time.Now().Format("2006/01/02 15:04:05"), "ProcessRead finish: ", i)

}

func (t *StreamTree) buildTree(i uint64, timet int64) *StreamNode {
	// 查找给定inode的节点
	blocks, path, size, err := GetInfoByInode(i)
	//_, path, err := GetInfoByInode(i)
	if err != nil {
		fmt.Printf("Error getting info by inode: %s\n", err)
		return nil
	}

	// 将路径拆分为 "/", "bookcorpus", "train"
	var parts []string

	pathParts := strings.Split(path, "/")
	for _, part := range pathParts {
		if part != "" {
			parts = append(parts, part)
		}
	}

	// fmt.Println(parts)

	currentNode := t.root
	length := len(parts)

	// 从根节点开始逐级向下匹配
	for k, part := range parts {
		found := false
		currentNode.noMu.Lock()
		if currentNode.noDict == nil {
			t.GenerateNoDictAndJudgeUnit(currentNode.inode)
		}
		currentNode.noMu.Unlock()

		// 要避免同一节点被多个并发协程多次创建
		currentNode.childListMu.Lock()
		for _, child := range currentNode.childList {
			if child.pathName == part+"/" {
				// 加入观察窗口
				currentNode.AddAccess(part, timet)
				currentNode.childListMu.Unlock()
				// 这里变了currentNode，所以需要释放锁
				currentNode = child
				found = true
				break
			}
		}

		// 如果在当前层级没有找到匹配项，创建一个新节点
		if !found {
			currentNode.childListMu.Unlock()
			// 找到当前的这个节点的Inode
			ino := t.FindInodeByLookup(currentNode.inode, part)
			// double check:如果映射
			t.inoMu.Lock()
			if _, e := t.m[ino]; e {
				currentNode.AddAccess(part, timet)
				currentNode = t.m[ino]
				t.inoMu.Unlock()
				continue
			}
			newNode := NewStreamNode(part, ino, currentNode)
			t.m[ino] = newNode
			t.inoMu.Unlock()
			// 加入观察窗口
			currentNode.AddAccess(part, timet)
			if k == length-1 {
				newNode.isFile = true
				if newNode.father.cacheUnitNode != nil {
					newNode.cacheUnitNode = newNode.father.cacheUnitNode
				} else {
					newNode.cacheUnitNode = newNode
					u := NewCacheUnit(newNode, t)
					go u.GetFileNumsAndSize()
					t.mu.Lock()
					t.nodeUnitDict[newNode] = u
					t.unitList = append(t.unitList, u)
					t.mu.Unlock()
				}
			}
			t.nodeNum++
			currentNode.childListMu.Lock()
			currentNode.childList = append(currentNode.childList, newNode)
			currentNode.childListMu.Unlock()
			currentNode = newNode
		}
	}

	//fmt.Println(i, ": reach 3")

	//fmt.Println(i, ": reach3")

	// 从文件节点开始记录
	node := currentNode

	// 这样在read时就不用再查询一次了
	node.blocks = blocks
	node.noLower = uint64(len(node.blocks)) //文件下块总数
	node.size = size

	return node

}

func (t *StreamTree) ProcessOpen(i uint64, timet int64) {
	//fmt.Println(i, ": reach 1")

	// TODO:剪枝时要删除对应的映射
	t.inodeLocksMu.Lock()
	mutex, exists := t.inodeLocks[i]
	if !exists {
		mutex = &sync.Mutex{}
		t.inodeLocks[i] = mutex
	}
	t.inodeLocksMu.Unlock()

	mutex.Lock()
	defer mutex.Unlock()

	//fmt.Println(i, ": reach1")

	// 查找给定inode的节点
	blocks, path, size, err := GetInfoByInode(i)
	//_, path, err := GetInfoByInode(i)
	if err != nil {
		fmt.Printf("Error getting info by inode: %s\n", err)
		return
	}

	//fmt.Println(i, ": reach 2 ", path)

	//fmt.Println(i, ": reach2")

	//path := "/bookcorpus/cache"

	// 将路径拆分为 "/", "bookcorpus", "train"
	var parts []string

	pathParts := strings.Split(path, "/")
	for _, part := range pathParts {
		if part != "" {
			parts = append(parts, part)
		}
	}

	// fmt.Println(parts)

	currentNode := t.root
	length := len(parts)

	// 从根节点开始逐级向下匹配
	for i, part := range parts {
		found := false
		currentNode.noMu.Lock()
		if currentNode.noDict == nil {
			t.GenerateNoDictAndJudgeUnit(currentNode.inode)
		}
		currentNode.noMu.Unlock()

		// 要避免同一节点被多个并发协程多次创建
		currentNode.childListMu.Lock()
		for _, child := range currentNode.childList {
			if child.pathName == part+"/" {
				// 加入观察窗口
				currentNode.AddAccess(part, timet)
				currentNode.childListMu.Unlock()
				// 这里变了currentNode，所以需要释放锁
				currentNode = child
				found = true
				break
			}
		}

		// 如果在当前层级没有找到匹配项，创建一个新节点
		if !found {
			currentNode.childListMu.Unlock()
			// 找到当前的这个节点的Inode
			ino := t.FindInodeByLookup(currentNode.inode, part)
			// double check:如果映射
			t.inoMu.Lock()
			if _, e := t.m[ino]; e {
				currentNode.AddAccess(part, timet)
				currentNode = t.m[ino]
				t.inoMu.Unlock()
				continue
			}
			newNode := NewStreamNode(part, ino, currentNode)
			t.m[ino] = newNode
			t.inoMu.Unlock()
			// 加入观察窗口
			currentNode.AddAccess(part, timet)
			if i == length-1 {
				newNode.isFile = true
				if newNode.father.cacheUnitNode != nil {
					newNode.cacheUnitNode = newNode.father.cacheUnitNode
				} else {
					newNode.cacheUnitNode = newNode
					u := NewCacheUnit(newNode, t)
					go u.GetFileNumsAndSize()
					t.mu.Lock()
					t.nodeUnitDict[newNode] = u
					t.unitList = append(t.unitList, u)
					t.mu.Unlock()
				}
			}
			t.nodeNum++
			currentNode.childListMu.Lock()
			currentNode.childList = append(currentNode.childList, newNode)
			currentNode.childListMu.Unlock()
			currentNode = newNode
		}
	}

	//fmt.Println(i, ": reach 3")

	//fmt.Println(i, ": reach3")

	// 从文件节点开始记录
	node := currentNode

	// 这样在read时就不用再查询一次了
	node.blocks = blocks
	node.noLower = uint64(len(node.blocks)) //文件下块总数
	node.size = size

	//fmt.Println("node: ", node.pathName)

	fmt.Println(time.Now().Format("2006/01/02 15:04:05"), "ProcessOpen finish: ", i)

	//
	//if judgePattern(currentNode.cacheUnitNode) == 1 {
	//	// 默认跨文件预取，跨文件夹预取风险大
	//	t.doPrefetch(currentNode)
	//
	//}

}

func (t *StreamTree) ProcessRead(i uint64, off uint64, size uint32, timet int64) {
	// 如果inode和锁的映射正在建立，不允许去读这个映射
	// 否则如果Open还未完成，Read这里获得锁一定是nil，这是不能接受的，我们需要保证Open-->Read
	t.inodeLocksMu.RLock()
	mutex, exists := t.inodeLocks[i]
	if !exists {
		// 这个inode的锁不存在说明没open，这是不应该出现的情况
		fmt.Println(i, ", error: may be not open")
	}
	t.inodeLocksMu.RUnlock()

	// inode串行执行，这也是正常的，多个Read并发访问本身会出现问题
	// 因为这个复杂度是线性的，应该执行很快
	mutex.Lock()
	defer mutex.Unlock()

	t.inoMu.Lock()
	node := t.m[i]
	t.inoMu.Unlock()

	// 记录IO_bound功能，从当前节点开始，向上遍历所有父节点
	for n := node; n != nil; n = n.father {
		// 更新当前节点的readTime
		n.readMu.Lock()
		n.readTime = append(n.readTime, timet)
		n.readMu.Unlock()

		//// 如果readTime长度超过最大值，则移除最早的元素
		//if len(currentNode.readTime) > maxReadTimeLength {
		//	currentNode.readTime = currentNode.readTime[1:] // 移除第一个元素
		//}
	}

	// 记录块读取功能
	//blocks, _, err := GetInfoByInode(i)
	//if err != nil {
	//	fmt.Println("Error getting info by inode: %s", err)
	//}

	//fmt.Println(i, ": reach4")

	var accumulatedOffset uint64 = 0
	var readEnd uint64 = off + uint64(size)

	blocks := node.blocks

	for j, block := range blocks {
		if accumulatedOffset+uint64(block.Len) > off && accumulatedOffset < readEnd {
			// 记录块号
			// 加入观察窗口
			node.AddAccess(uint32(j), timet)
			//fmt.Println("block add1: ", j)
			t.mu.RLock()
			u, e := t.nodeUnitDict[node.cacheUnitNode]
			t.mu.RUnlock()
			if e {
				u.AddItem(CacheItem{block.Key, block.Size})
			}
			//fmt.Println("block add2: ", j)
		}
		accumulatedOffset += uint64(block.Len)
		if accumulatedOffset >= readEnd {
			break
		}
	}

	fmt.Println(time.Now().Format("2006/01/02 15:04:05"), "ProcessRead finish: ", i)

}

// DispatchServer 服务IO-busy的http server
func (t *StreamTree) DispatchServer() {
	http.HandleFunc("/dataset", func(w http.ResponseWriter, r *http.Request) {
		if r.Method == http.MethodGet {
			w.Header().Set("Content-Type", "application/json")
			jsonBytes, err := json.Marshal(t.isDatasetBusy)
			if err != nil {
				http.Error(w, err.Error(), http.StatusInternalServerError)
				return
			}
			w.Write(jsonBytes)
		} else {
			http.Error(w, "Invalid request method", http.StatusMethodNotAllowed)
		}
	})

	// 在8082端口启动服务器
	fmt.Println("Server starting on port 8082...")
	http.ListenAndServe(":8082", nil)
}

func (t *StreamTree) CalIOBusyTime() {
	for {
		//t.mu.Lock()
		fmt.Println("exec a IO Busy Calculation")

		results := make(map[string]float64)

		now := time.Now().Unix()
		// 从根节点开始递归
		t.calculateNodeIOBusyTime(t.root, "", results, now)

		//t.mu.Unlock()

		// hardcode映射数据集
		if r, exists := results["/ImageNet/"]; exists {
			t.isDatasetBusy["/ImageNet/"] = r
			//if r > 0.90 {
			//	t.isDatasetBusy["/ImageNet/"] = 1
			//} else {
			//	t.isDatasetBusy["/ImageNet/"] = 0
			//}
		}

		if r, exists := results["/MITPlaces/"]; exists {
			t.isDatasetBusy["/MITPlaces/"] = r
			//if r > 0.90 {
			//	t.isDatasetBusy["/MITPlaces/"] = 1
			//} else {
			//	t.isDatasetBusy["/MITPlaces/"] = 0
			//}
		}

		// 休眠指定的时间，3秒检查一次IOBusy
		time.Sleep(30 * time.Second)
	}
}

func (t *StreamTree) calculateNodeIOBusyTime(node *StreamNode, path string, results map[string]float64, now int64) {
	if node == nil {
		return
	}

	if node.isFile == true {
		return
	}

	readTimes := uniqueTimestamps(node.readTime)
	if len(readTimes) > 0 {
		// 找到最小和最大时间戳
		// minTime, maxTime := readTimes[0], now
		totalTime := CheckBusyTime

		// 计算比例
		var ratio float64 = float64(len(readTimes)) / float64(totalTime)
		// 格式化并添加到结果
		results[path+node.pathName] = ratio

	}

	// 清空当前节点的readTime数组
	node.readTime = make([]int64, 0)

	// 递归处理子节点
	for _, child := range node.childList {
		t.calculateNodeIOBusyTime(child, path+node.pathName, results, now)
	}
}

// uniqueTimestamps 返回时间戳数组中不重复的时间戳
func uniqueTimestamps(timestamps []int64) []int64 {
	unique := make(map[int64]bool)
	var result []int64
	for _, timestamp := range timestamps {
		if _, found := unique[timestamp]; !found {
			unique[timestamp] = true
			result = append(result, timestamp)
		}
	}
	return result
}

// Prune 定期检查剪枝
func (t *StreamTree) Prune() {
	for {
		// 每30秒检查一次
		time.Sleep(PruneTime * time.Second)

		//t.mu.Lock()

		// 检查节点数是否超过阈值
		if t.nodeNum > 50000 {
			t.pruneNode(t.root, time.Now().Unix())
		}

		//t.mu.Unlock()
	}
}

func (t *StreamTree) pruneNode(node *StreamNode, now int64) {
	if node == nil {
		return
	}

	// TODO：check两个版本的区别
	//// 如果当前节点最后一次读取时间超过60秒，或者从未读取过且创建时间超过60秒
	//if (len(node.readTime) > 0 && now-node.readTime[len(node.readTime)-1] > 10) || (len(node.readTime) == 0 && now-node.cTime > 10) {
	//	// 直接剪掉此节点及其所有子节点
	//	t.recursiveRemoveNode(node)
	//	return // 剪枝后返回，不再对子节点进行递归判断
	//}
	// 如果当前节点最后一次读取时间超过60秒，或者从未读取过且创建时间超过60秒
	if len(node.readTime) > 0 && now-node.readTime[len(node.readTime)-1] > 10 {
		// 直接剪掉此节点及其所有子节点
		t.recursiveRemoveNode(node)
		return // 剪枝后返回，不再对子节点进行递归判断
	}

	// 否则递归检查子节点
	for _, child := range node.childList {
		t.pruneNode(child, now)
	}
}

// recursiveRemoveNode 递归移除节点及其所有子节点
func (t *StreamTree) recursiveRemoveNode(node *StreamNode) {
	if node == nil {
		return
	}

	// 递归删除所有子节点
	for _, child := range node.childList {
		t.recursiveRemoveNode(child)
	}

	// 如果此节点有父节点(考虑root)，从父节点的子列表中移除此节点
	if node.father != nil {
		node.father.childListMu.Lock()
		for i, child := range node.father.childList {
			if child == node {
				node.father.childList = append(node.father.childList[:i], node.father.childList[i+1:]...)
				break
			}
		}
		node.father.childListMu.Unlock()
	}

	node.father = nil

	// 从映射中删除
	t.inoMu.Lock()
	if _, exists := t.m[node.inode]; exists {
		delete(t.m, node.inode)
	}
	t.inoMu.Unlock()

	t.inodeLocksMu.Lock()
	if _, exists := t.inodeLocks[node.inode]; exists {
		delete(t.inodeLocks, node.inode)
	}
	t.inodeLocksMu.Unlock()

	// 更新节点计数
	t.nodeNum--
}

// ProcessCacheUnit 对cacheUnit的处理
func (t *StreamTree) ProcessCacheUnit() {

	for {
		time.Sleep(TuneTime * time.Second)

		fmt.Println(time.Now().Format("2006/01/02 15:04:05"), "before tuning: ")

		for _, unit := range t.unitList {
			node := unit.node
			path := getPath(node)
			fmt.Println("path: ", path, ", capacity: ", unit.capacity)
		}

		// 模式判别
		for _, unit := range t.unitList {
			unit.pattern = judgePattern(unit.node)
		}

		// 调整缓存大小
		t.TuneCacheCapacity()

		//fmt.Println("unit num: ", len(t.unitList))

		fmt.Println(time.Now().Format("2006/01/02 15:04:05"), "after tuning: ")

		for _, unit := range t.unitList {
			node := unit.node
			path := getPath(node)
			fmt.Println("path: ", path, ", capacity: ", unit.capacity, ", files: ", unit.files, ", pattern: ", unit.pattern, ", margin: ", unit.margin)
		}
	}
}

func getPath(node *StreamNode) string {
	if node.father == nil {
		return node.pathName
	} else {
		return getPath(node.father) + node.pathName
	}

}

func (t *StreamTree) TuneCacheCapacity() {
	// TODO: 最大size，最小size

	// 因为并行处理，可能出现一个cache的files和size还没计算完正好赶上一次tune的情况
	// 没有计算完的话，不参与本次调整
	var unitList = make([]*CacheUnit, 0)

	// 先筛选一轮，筛掉files和size没统计完的unit
	// 其他的计算margin benefit后加入unitList
	for _, u := range t.unitList {
		// 说明file和size没统计完成， 不参与本轮计算
		if u.files == 0 && u.size == 0 {
			continue
		} else {
			avgSize := float64(u.size) / float64(u.files)
			if avgSize < float64(4*1024*1024) {
				//小文件：最大大小是文件总大小
				u.maxSize = u.size
			} else {
				//大文件：统计叶子节点（文件），总大小
				u.maxSize = SumLeafSize(u.node)
			}
			//计算边际收益，加入unitList
			u.CalculateMarginBenefit()
			unitList = append(unitList, u)
		}
	}

	// 对cacheWithPattern进行排序
	sort.Slice(unitList, func(i, j int) bool {
		return unitList[i].margin > unitList[j].margin
	})

	var cacheToTuneByStep []*CacheUnit
	// 遍历已经确定模式的缓存单元
	for _, u := range unitList {
		if u.margin == -1.0 {
			// Stride Pattern的情况
			//TODO:根据预取调整，不一定是定值
			goalSize := min(uint64(StrideSize), u.maxSize)
			if u.capacity > goalSize {
				t.freeCapacity += u.capacity - goalSize
			} else {
				t.freeCapacity -= goalSize - u.capacity
			}
			u.TuneCapacityAndFree(goalSize)
		} else {
			// 先把超出最大容量（可以理解为数据集大小）的回收一下
			if u.capacity >= u.maxSize {
				goalSize := u.maxSize
				t.freeCapacity += u.capacity - goalSize
				u.TuneCapacityAndFree(goalSize)
			}
			cacheToTuneByStep = append(cacheToTuneByStep, u)

		}
	}

	// 接下来的调整步骤
	s := len(cacheToTuneByStep)
	sizeToTuneThisRound := uint64((s / 2) * CapacityToTune)
	goalSize := make([]uint64, len(cacheToTuneByStep))

	for i := range cacheToTuneByStep {
		goalSize[i] = cacheToTuneByStep[i].capacity
	}

	// 从后向前开始回收
	if t.freeCapacity < sizeToTuneThisRound {
		for i := len(cacheToTuneByStep) - 1; i >= 0; i-- {
			u := cacheToTuneByStep[i]
			sizeCanRecycle := min(u.capacity-MinCacheSize, sizeToTuneThisRound-t.freeCapacity)
			goalSize[i] -= sizeCanRecycle
			t.freeCapacity += sizeCanRecycle
			//回收足够的内存就可以退出
			if t.freeCapacity == sizeToTuneThisRound {
				break
			}
		}
	}

	for i, u := range cacheToTuneByStep {
		sizeCanAllocate := min(t.freeCapacity, u.maxSize-goalSize[i])
		t.freeCapacity -= sizeCanAllocate
		goalSize[i] += sizeCanAllocate
		if t.freeCapacity == 0 {
			break
		}
	}

	// 调整缓存大小
	for i, c := range cacheToTuneByStep {
		c.TuneCapacityAndFree(goalSize[i])
	}
}

// judgePattern
func judgePattern(node *StreamNode) uint8 {
	accessWindow := node.accessWindow
	//fmt.Println(getPath(node), " accessWindow: ", accessWindow)

	var convertedWindow []uint32

	if node.isFile {
		for _, acc := range accessWindow {
			if name, ok := acc.name.(uint32); ok {
				convertedWindow = append(convertedWindow, name)
			} else {
				fmt.Println("convert block id error")
			}
		}
	} else {
		for _, acc := range accessWindow {
			if name, ok := acc.name.(string); ok {
				node.noMu.RLock()
				convertedWindow = append(convertedWindow, node.noDict[name])
				node.noMu.RUnlock()
			} else {
				fmt.Println("convert file name error")
			}
		}
	}

	//fmt.Println(getPath(node), " convertedWindow: ", convertedWindow)

	if JudgeIfStridePattern(convertedWindow) {
		return 1
	}

	// 访问的文件数很少, 可能是在对大文件进行集中访问
	if len(accessWindow) < LeastLengthToJudge {
		//根据子节点的模式进行判断，重要！！
		if node.isFile {
			return 3
		} else {
			childPattern := make([]uint8, 0)
			var rst uint8
			rst = 3
			for _, child := range node.childList {
				// 找到一个子节点
				childPattern = append(childPattern, judgePattern(child))
				for _, p := range childPattern {
					// 优先判断为r
					if p == 2 {
						rst = 2
						break
					} else if p == 1 {
						rst = 1
						break
					}
				}
			}
			return rst
		}
	}

	// 传入下层item总数（目录、文件、文件块）
	if JudgeIfRandomPattern(convertedWindow, node.noLower) {
		return 2
	}

	// 默认为 3（Hot-spot Pattern）
	return 3

}

// JudgeIfStridePattern 判断Stride模式
func JudgeIfStridePattern(window []uint32) bool {
	//TODO: 仅在文件层面呈现Stride，但块层面不是连续读，此时也是不是Stride（TPCDS有partition的情况）
	size := len(window)
	if size < 20 {
		return false
	}
	flag := true
	difference := make([]int, 0)
	for i := size - 1; i >= size-5; i-- {
		diff := int(window[i] - window[i-1])
		difference = append(difference, diff)
	}

	for i := 0; i < len(difference)-1; i++ {
		if difference[i] != difference[i+1] {
			flag = false
			break
		}
	}
	return flag
}

func JudgeIfRandomPattern(window []uint32, n uint64) bool {
	size := len(window)
	if size < 20 {
		return false
	}
	p := CalculateGapDistributionGaussian(window)
	return JudgeDistribution(p, n)
}

func CalculateGapDistributionGaussian(window []uint32) Pair {
	var avg, std float64
	var nrSample uint32
	nrSample = 0
	const defaultStd, minStd = 10.0, 3.0
	size := len(window)

	for i := size - 1; i >= size-10; i-- {
		oldAvg, oldStd := avg, std
		gap := float64(absDiff(window[i], window[i-1]))
		//fmt.Println("gap: ", gap)
		var newAvg, newStd float64
		if nrSample == 0 {
			newAvg = gap
			newStd = defaultStd
		} else {
			newAvg = (oldAvg*float64(nrSample) + gap) / (float64(nrSample) + 1)
			newStd = math.Sqrt((float64(nrSample)*(math.Pow(oldStd, 2)+math.Pow(newAvg-oldAvg, 2)) + math.Pow(newAvg-gap, 2)) / (float64(nrSample) + 1))
			newStd = math.Max(newStd, minStd)
		}
		avg, std = newAvg, newStd
		nrSample++
	}
	return Pair{avg, std}
}

func JudgeDistribution(p Pair, n uint64) bool {
	// 假定 nrFileTotal 是 CacheUnit 的一个字段
	// 总块数
	if p.First > float64(n)*0.26 && p.First < float64(n)*0.45 {
		return true
	}
	//fmt.Println("avg: ", p.First)
	// TODO:增加方差判别
	return false
}

type CacheItem struct {
	key   string // 块名
	value uint32 // 块大小
}

type LRU struct {
	capacity uint64
	list     *list.List
	elements map[string]*list.Element
	used     uint64
}

func NewLRU(capacity uint64) *LRU {
	return &LRU{
		capacity: capacity,
		list:     list.New(),
		elements: make(map[string]*list.Element),
		used:     0,
	}
}

// CacheUnit 表示缓存单元。
type CacheUnit struct {
	tree        *StreamTree
	node        *StreamNode
	capacity    uint64
	used        uint64
	cache       *LRU
	reuseWindow *LRU
	pattern     uint8 // 初始：1, stride：1， random：2，hot-spot：3
	margin      float64
	files       uint64 //总文件数
	size        uint64 //总大小，通过GetFileNumsAndSize递归获得
	acc         uint32 //本轮总访问次数
	reuse       uint32 //被重用数量
	maxSize     uint64 //每轮的最大大小
	mu          sync.Mutex
}

func NewCacheUnit(node *StreamNode, tree *StreamTree) *CacheUnit {
	u := &CacheUnit{
		tree:     tree,
		node:     node,
		capacity: InitialCapacity, //先给一个初始的大小
		used:     0,
		margin:   0,
		files:    0,
		size:     0,
		acc:      0,
		reuse:    0,
		pattern:  0,
		maxSize:  0,
	}

	u.cache = NewLRU(u.capacity)
	u.reuseWindow = NewLRU(ReuseWindowSize)

	return u
}

func (u *CacheUnit) GetFileNumsAndSize() {
	file, size, err := recursiveGetSizeByInode(u.node.inode)
	if err != nil {
		fmt.Printf("Error getting info by inode: %s\n", err)
		return
	}
	u.files = file
	u.size = size
}

func (u *CacheUnit) AddItem(item CacheItem) {
	// 记录一次访问，为了衡量访问速度
	u.mu.Lock()
	defer u.mu.Unlock()
	//fmt.Println("cacheunit: ", u.node.pathName, "\n",
	//	"item key: ", item.key, "\n",
	//	"size: ", item.value, "\n",
	//	"unit capacity: ", u.cache.capacity, "\n",
	//	"unit used: ", u.cache.used)
	//fmt.Println(item.key, ": reach 1")

	//trimmed := strings.TrimPrefix(item.key, "jfs/")
	//path := filepath.Join(u.tree.cacheDir, cacheDir, trimmed)
	//fmt.Println(path, ": begin")
	u.acc += 1
	//fmt.Println(item.key, ": reach 2")
	// 检查item是否已经在缓存中
	if elem, found := u.cache.elements[item.key]; found {
		// 如果已经在缓存中，移动到链表前面
		u.cache.list.MoveToFront(elem)
		//// 更新已用空间（减去旧大小，加上新大小）
		//u.cache.used -= uint64(elem.Value.(*CacheItem).value) + EntrySize
		//u.cache.used += uint64(item.value) + EntrySize
		//// 更新元素值
		//elem.Value.(*CacheItem).value = item.value + EntrySize
		return
	}

	//fmt.Println(item.key, ": reach 3")

	// 不在u.cache中，但是在reuseWindow中，重用次数+1
	if _, found := u.cache.elements[item.key]; found {
		u.reuse += 1
	}

	// 检查添加新项是否会超出容量
	for u.cache.used+uint64(item.value)+EntrySize > u.cache.capacity {
		// 如果pattern是random，则直接退出，uniform
		if u.pattern == 2 {
			//TODO:是否需要滞后删除
			trimmed := strings.TrimPrefix(item.key, "jfs/")
			path := filepath.Join(u.tree.cacheDir, cacheDir, trimmed)
			addToPendingDeletions(path, 2)
			// go os.Remove(path)
			return
		}
		// 移除最不常用的块
		u.removeOldestItem()
	}

	//fmt.Println(item.key, ": reach 4")

	// 将新项添加到链表前面
	newElem := u.cache.list.PushFront(&item)
	// 在哈希表中创建条目
	u.cache.elements[item.key] = newElem
	// 更新已用空间
	u.cache.used += uint64(item.value) + EntrySize

	//fmt.Println(item.key, ": reach 5")

	//fmt.Println(path, ": end")

}

// removeOldestItem 从LRU缓存中移除最不常用的项
func (u *CacheUnit) removeOldestItem() {
	oldest := u.cache.list.Back()
	if oldest != nil {
		item := oldest.Value.(*CacheItem)
		u.cache.used -= uint64(item.value) + EntrySize
		u.cache.list.Remove(oldest)
		fmt.Println("delete key: ", item.key)
		delete(u.cache.elements, item.key)
		trimmed := strings.TrimPrefix(item.key, "jfs/")
		path := filepath.Join(u.tree.cacheDir, cacheDir, trimmed)
		addToPendingDeletions(path, 2)
		// go os.Remove(path)

		// 三种pattern都维护ReusWindow，这是为了防止模式的转换
		u.addToReuseWindow(*item)

		//if u.reuseWindow != nil {
		//	//判断是否存在，实际上判断是否是hot-spot，将删除的旧项添加到reuseWindow中
		//	u.addToReuseWindow(*item)
		//}
	}
}

func (u *CacheUnit) addToReuseWindow(item CacheItem) {
	for u.reuseWindow.used+uint64(item.value) > u.reuseWindow.capacity {
		u.removeOldestFromReuseWindow()
	}

	// 将项添加到reuseWindow
	newElem := u.reuseWindow.list.PushFront(&item)
	u.reuseWindow.elements[item.key] = newElem
	u.reuseWindow.used += uint64(item.value)

}

func (u *CacheUnit) removeOldestFromReuseWindow() {
	oldest := u.reuseWindow.list.Back()
	if oldest != nil {
		item := oldest.Value.(*CacheItem)
		u.reuseWindow.used -= uint64(item.value)
		u.reuseWindow.list.Remove(oldest)
		delete(u.reuseWindow.elements, item.key)
	}
}

// SumLeafNoLower 统计所有叶子节点（文件）的总文件块数
func SumLeafNoLower(node *StreamNode) uint64 {
	if node == nil {
		return 0
	}
	// Check if the node is a leaf node (no children)
	if len(node.childList) == 0 {
		// This is a leaf node
		return node.noLower
	}
	// If not a leaf, sum noLower for all leaf children
	var sum uint64 = 0
	for _, child := range node.childList {
		sum += SumLeafNoLower(child)
	}
	return sum
}

// SumLeafSize 统计所有叶子节点（文件）的大小
func SumLeafSize(node *StreamNode) uint64 {
	if node == nil {
		return 0
	}
	// Check if the node is a leaf node (no children)
	if len(node.childList) == 0 {
		// This is a leaf node
		return node.size
	}
	// If not a leaf, sum noLower for all leaf children
	var sum uint64 = 0
	for _, child := range node.childList {
		sum += SumLeafSize(child)
	}
	return sum
}

func (u *CacheUnit) CalculateMarginBenefit() {
	switch u.pattern {
	case 1:
		// 人为规定一个很低的值, -1 代表不能产生收益
		u.margin = -1

	// 统一到减少的未命中次数
	case 2:
		// 估计块数量， 以及能够带来的命中率
		avgSize := float64(u.size) / float64(u.files)

		fmt.Println("avgSize: ", avgSize)

		// 4 * 1024 * 1024 bytes = 4MB
		if avgSize < float64(4*1024*1024) {
			// 小文件数据集
			//fmt.Println("small files!")
			//fmt.Println("files: ", u.files, "avgSize: ", avgSize, "acc: ", u.acc)
			u.margin = (1 / float64(u.files)) / avgSize * float64(u.acc)
		} else {
			// 大文件数据集, 估计值
			// 只能统计访问过的文件，e.g. Dataset的cache，其他arrow不被访问

			sum := SumLeafNoLower(u.node)
			u.margin = (1 / float64(sum)) / (4 * 1024 * 1024) * float64(u.acc)

		}
	case 3:
		//基于ReuseWindow判断
		u.margin = float64(u.reuse)
	}

}

func (u *CacheUnit) TuneCapacityAndFree(goalSize uint64) {
	u.mu.Lock()
	defer u.mu.Unlock()

	// 如果是扩容，直接更新 cacheSize
	if goalSize > u.capacity {
		u.capacity = goalSize
		return
	}

	// 需要释放缓存缓存大小
	var capacityToFree uint64
	if u.cache.used < goalSize {
		capacityToFree = 0
	} else {
		capacityToFree = u.cache.used - goalSize
	}

	for capacityToFree > 0 {
		// 如果缓存已经处于或低于期望的容量，跳出循环。
		if u.cache.used <= goalSize {
			break
		}

		// 从缓存中移除最老的条目。
		oldest := u.cache.list.Back()
		if oldest == nil {
			break // 没有更多的项可以移除, 以为着缓存里没有任何条目
		}

		item := oldest.Value.(*CacheItem)
		u.cache.used -= uint64(item.value) + EntrySize
		u.cache.list.Remove(oldest)
		delete(u.cache.elements, item.key)

		// 从缓存目录中删除
		// TODO: 是否需要滞后
		trimmed := strings.TrimPrefix(item.key, "jfs/")
		path := filepath.Join(u.tree.cacheDir, cacheDir, trimmed)
		addToPendingDeletions(path, 2)
		//go os.Remove(path)

		// 重新计算还需要释放的容量。
		capacityToFree = u.cache.used - goalSize
	}

	u.capacity = goalSize
	// TODO:这一句可能还要检查
	u.cache.capacity = u.capacity

}

//func (t *StreamTree) remove(key string) {
//	trimmed := strings.TrimPrefix(key, "jfs/")
//	path := filepath.Join(t.cacheDir, cacheDir, trimmed)
//
//	// 尝试删除文件
//	err := os.Remove(path)
//	if err != nil {
//		if os.IsNotExist(err) {
//			// 如果文件不存在，等待一段时间后重试
//			time.Sleep(1 * time.Second) // 延迟1秒再次删除
//			err = os.Remove(path)
//		}
//	}
//}

type deleteEntry struct {
	path        string
	attempt     int
	maxAttempts int
}

// addToPendingDeletions 添加路径到待删除映射中
func addToPendingDeletions(path string, maxAttempts int) {
	pendingDeletions.Store(path, deleteEntry{
		path:        path,
		attempt:     0,
		maxAttempts: maxAttempts,
	})
}

// removeFile 定期尝试删除文件
func removeFile() {
	ticker := time.NewTicker(5 * time.Second) // 每10秒执行一次
	defer ticker.Stop()

	for range ticker.C {
		pendingDeletions.Range(func(key, value interface{}) bool {
			entry := value.(deleteEntry)
			if err := os.Remove(entry.path); err != nil {
				// 如果删除失败，增加尝试次数
				entry.attempt++
				fmt.Printf("Failed to remove %s, attempt %d\n", entry.path, entry.attempt)
				if entry.attempt >= entry.maxAttempts {
					// 达到最大尝试次数，放弃删除
					fmt.Printf("Giving up on %s after %d attempts\n", entry.path, entry.attempt)
					pendingDeletions.Delete(key)
				} else {
					// 更新entry信息
					pendingDeletions.Store(key, entry)
				}
			} else {
				// 如果成功删除，从映射中移除这个路径
				fmt.Printf("Successfully removed %s\n", entry.path)
				pendingDeletions.Delete(key)
			}
			return true // 继续迭代
		})
	}
}
