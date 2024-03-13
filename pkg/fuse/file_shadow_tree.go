package fuse

import (
	"container/list"
	"github.com/hanwen/go-fuse/v2/fuse"
	"math"
	"os"
	"sort"
	"strings"
)

// 静态变量，对包级别是全局的
const (
	StrideCacheSize = 10
	MinCacheSize    = 200

	CapacityToTune     = 32
	LeastLengthToJudge = 50
	BlockSize          = 4 << 20
	accessWindowSize   = 30
	MaxCapacity        = 4194304 // 最大缓存
)

type Pair struct {
	First  float64
	Second float64
}

type Range struct {
	Start int
	End   int
}

func min(a, b uint64) uint64 {
	if a < b {
		return a
	}
	return b
}

// FileShadowNode 表示文件树中的一个节点。
type FileShadowNode struct {
	// filePathName string
	pathName         string
	father           *FileShadowNode
	cacheUnitNode    *FileShadowNode
	NumSub           uint64 //子文件或目录数量
	maxI             uint64
	minI             uint64
	childList        []*FileShadowNode
	inode            Ino //对应的Inode
	isManagementNode bool
	isOpen           bool
	length           uint64 // 主要记录文件
	hasJudged        bool   //这个节点是否已经作为上层文件夹被判断过
}

func NewFileShadowNode(p string, i Ino, f *FileShadowNode) *FileShadowNode {
	return &FileShadowNode{
		pathName:         p,
		father:           f,
		cacheUnitNode:    nil,
		NumSub:           0, // 次级目录文件总数
		maxI:             0,
		minI:             math.MaxInt64,
		childList:        make([]*FileShadowNode, 0),
		inode:            i,
		isManagementNode: false,
		isOpen:           false,
		hasJudged:        false,
	}
}

// FileShadowTree 用于管理文件影子树。
type FileShadowTree struct {
	// filePathMaintianed和accessNum都是和访问数相关的类变量
	// filePathMaintained是维护的总路径数，主要用于负载控制
	// accessNum是访问总数，用于决定何时进行cache capacity tuning
	fs                 *fileSystem
	nodeNum            int
	filePathMaintained int
	accessNum          int
	root               *FileShadowNode
	unitNodeList       []*FileShadowNode
	nodeToCache        map[*FileShadowNode]*CacheUnit
	totalCapacity      int
	freeCapacity       uint64
	newCacheUnitSize   int
	accessToTune       int                     // 调整的轮数
	m                  map[Ino]*FileShadowNode // Ino和*FileShadowNode的映射关系
}

func NewFileShadowTree(fs *fileSystem) *FileShadowTree {
	tree := &FileShadowTree{
		fs:               fs,
		nodeNum:          0,
		root:             NewFileShadowNode("/", 1, nil), // 初始化 root 节点
		unitNodeList:     make([]*FileShadowNode, 0),
		nodeToCache:      make(map[*FileShadowNode]*CacheUnit),
		totalCapacity:    6144,
		freeCapacity:     6144,
		newCacheUnitSize: 512,
		accessToTune:     200,
		m:                make(map[Ino]*FileShadowNode),
	}
	tree.m[1] = tree.root
	return tree
}

// GenerateNode 根据fuse.Lookup的分解生成节点建树，使用Inode没有重名冲突
func (t *FileShadowTree) GenerateNode(name string, ip Ino, ic Ino, out *fuse.EntryOut) {
	// TODO: 可以根据fuse.EntryOut实现更多功能

	_, exists := t.m[ic]
	if exists {
		return
	}

	// 该节点的父母不存在
	parent, exists := t.m[ip]
	if !exists {
		return
	}

	// 建立父节点和子节点关系
	node := NewFileShadowNode(name, ic, parent)
	parent.childList = append(t.m[ip].childList, node)
	t.m[ic] = node

}

// 调用一个接口来释放缓存
func (t *FileShadowTree) manuallyRemove(ino Ino, offset uint64, size uint32) {
	var oin *fuse.OpenIn
	oin.Pid = uint32(os.Getpid())
	oin.Gid = uint32(os.Getgid())
	oin.Uid = uint32(os.Getuid())
	var oout *fuse.OpenOut
	oin.NodeId = uint64(ino)
	fakeCancel := make(chan struct{})
	_ = t.fs.manuallyOpen(fakeCancel, oin, oout)
	fh := oout.Fh

	var rin *fuse.ReadIn
	var fakeBuf []byte // 假buf
	rin.Pid = uint32(os.Getpid())
	rin.Gid = uint32(os.Getgid())
	rin.Uid = uint32(os.Getuid())
	// 把要删除的偏移给放进去ReadIn的参数里去
	rin.NodeId = uint64(ino) //实际要释放的NodeId
	rin.Offset = offset
	rin.Size = size
	rin.Fh = fh
	// 借用ReadIn假调用一次获得rSlice来remove缓存
	_, _ = t.fs.Remove(fakeCancel, rin, fakeBuf)

}

func (t *FileShadowTree) TuneCacheCapacity() {
	// 创建一个用于存储已经确定模式的CacheUnit的切片
	var cacheWithPattern []*CacheUnit

	// 遍历已经记录的最后一级节点
	for _, n := range t.unitNodeList {
		c := t.nodeToCache[n]
		c.JudgeThePattern()
		if c.pattern != 'u' {
			c.CalculateMarginBenefit()
			cacheWithPattern = append(cacheWithPattern, c)
		}
	}

	// 对cacheWithPattern进行排序
	sort.Slice(cacheWithPattern, func(i, j int) bool {
		return cacheWithPattern[i].marginBenefit > cacheWithPattern[j].marginBenefit
	})

	var cacheToTuneByStep []*CacheUnit

	// 遍历已经确定模式的缓存单元
	for _, c := range cacheWithPattern {
		if c.marginBenefit == -1.0 {
			if c.pattern == 's' {
				goalSize := StrideCacheSize
				if c.cacheSize != uint64(goalSize) {
					t.freeCapacity += c.cacheSize - uint64(goalSize)
					c.TuneCapacityAndFree(uint64(goalSize))
				}
			}
			if c.pattern == 't' {
				continue
			}
		} else {
			cacheToTuneByStep = append(cacheToTuneByStep, c)
		}
	}

	// 接下来的调整步骤
	s := len(cacheToTuneByStep)
	sizeToTuneThisRound := uint64((s / 2) * CapacityToTune)
	goalSize := make([]uint64, len(cacheToTuneByStep))

	for i := range cacheToTuneByStep {
		goalSize[i] = cacheToTuneByStep[i].cacheSize
	}

	// 从前开始回收
	if t.freeCapacity < sizeToTuneThisRound {
		for i := len(cacheToTuneByStep) - 1; i >= 0; i-- {
			c := cacheToTuneByStep[i]
			sizeCanRecycle := min(c.cacheSize-MinCacheSize, sizeToTuneThisRound-t.freeCapacity)
			goalSize[i] -= sizeCanRecycle
			t.freeCapacity += sizeCanRecycle
			if t.freeCapacity == sizeToTuneThisRound {
				break
			}
		}
	}

	sizeRemain := sizeToTuneThisRound
	for i := range cacheToTuneByStep {
		sizeCanAllocate := min(sizeRemain, min(CapacityToTune, MaxCapacity-goalSize[i]))
		sizeRemain -= sizeCanAllocate
		t.freeCapacity -= sizeCanAllocate
		goalSize[i] += sizeCanAllocate
		if sizeRemain == 0 {
			break
		}
	}

	// 调整缓存大小
	for i, c := range cacheToTuneByStep {
		c.TuneCapacityAndFree(goalSize[i])
	}
}

func (n *FileShadowNode) judgeSementic() bool {
	arr := make([]string, 0)
	for _, node := range n.childList {
		arr = append(arr, node.pathName)
	}

	if len(arr) == 0 {
		return false
	}

	// TODO：可以进一步细化方法
	first := arr[0][:3] // 取第一个字符串的前三位作为比较基准
	for _, str := range arr {
		if len(str) < 3 || !strings.HasPrefix(str, first) {
			return false
		}
	}
	return true
}

// processOpen 根据fuse.Open打开文件进行处理
func (t *FileShadowTree) processOpen(i Ino, attr *Attr) {
	n, exists := t.m[i]
	if !exists {
		return
	}

	// 调整轮次
	t.accessNum++
	if t.accessNum%200 == 0 {
		t.TuneCacheCapacity()
	}

	n.isOpen = true
	n.length = attr.Length // 记录一个文件的大小

	f := n.father
	ff := f.father

	// 如果上上层节点已经作为一个缓存管理单元管理
	if c, exists := t.nodeToCache[ff]; exists {
		// 如果上上层节点已经作为一个大的缓存单元
		n.cacheUnitNode = ff
		c.accessWindow = append(c.accessWindow, c.dirMap[f])
	} else {
		// 如果上上层节点没有判断是否能作为缓存单元
		// 判断是否可以作为缓存管理单元, 如果已经判断过不行为false，不能重复判断
		if !ff.hasJudged {
			// 判断语义信息
			if ff.judgeSementic() {
				// 如果存在语义信息,建立一个新的newCache
				newCache := NewCacheUnit(ff, t)
				newCache.updateInformation()
				newCache.accessWindow = append(newCache.accessWindow, newCache.dirMap[f])
				n.cacheUnitNode = ff
				t.nodeToCache[ff] = newCache
			}

			ff.hasJudged = true
		}

		// 上上层节点不能作为缓存单元
		// 判断上层节点
		if c1, e1 := t.nodeToCache[f]; e1 {
			// 上层已经作为节点
			n.cacheUnitNode = f
			c1.accessWindow = append(c1.accessWindow, uint64(i))
		} else {
			newCache := NewCacheUnit(f, t)
			newCache.nrFileTotal = f.NumSub
			newCache.accessWindow = append(newCache.accessWindow, uint64(i))
			t.nodeToCache[f] = newCache
			n.cacheUnitNode = f

		}

	}
}

func (t *FileShadowTree) processRead(ino Ino, offset uint64, size uint32) {
	// 计算块号，保存在文件节点下，自管理缓存
	// 计算块号和大小
	file, exists := t.m[ino]
	if !exists {
		return
	}
	unit := t.nodeToCache[file.cacheUnitNode]

	firstIndx := offset / BlockSize                     // 第一个块编号
	lastIndx := (offset + uint64(size) - 1) / BlockSize // 最后一个块编号
	lastBlock := (t.m[ino].length - 1) / BlockSize
	unit.nrAccess += lastBlock + 1 //记录访问的块号

	// random pattern需要单独的处理机制Uniform
	if unit.pattern == 'r' {
		for i := firstIndx; i < lastIndx; i++ {
			if unit.cache.used+BlockSize <= unit.cache.capacity {
				unit.cache.used += BlockSize
				unit.cache.Add(fileBlockPair{ino, i}, BlockSize)
			} else {
				t.manuallyRemove(ino, uint64(i*BlockSize), BlockSize)
				break
			}
		}

		if lastIndx == lastBlock {
			//最后一个块不完整
			s := uint32((t.m[ino].length-1)%BlockSize + 1)
			if unit.cache.used+uint64(s) <= unit.cache.capacity {
				unit.cache.used += uint64(s)
				unit.cache.Add(fileBlockPair{ino, lastIndx}, s)
			} else {
				t.manuallyRemove(ino, lastIndx*BlockSize, s)
				return
			}
		} else {
			// 最后一个块完整
			if unit.cache.used+BlockSize <= unit.cache.capacity {
				unit.cache.used += BlockSize
				unit.cache.Add(fileBlockPair{ino, lastIndx}, BlockSize)
			} else {
				t.manuallyRemove(ino, lastIndx*BlockSize, BlockSize)
				return
			}
		}
		return
	}

	// 正常按LRU的逻辑处理
	// 更新CacheUnit的cache
	// 如果读到最后一个块
	// 从 firstIndx 到 lastIndx 遍历
	for i := firstIndx; i < lastIndx; i++ {
		unit.cache.used += BlockSize
		fileBlock := fileBlockPair{ino, i}
		if _, exists := unit.reuseWindow.m[fileBlock]; exists {
			unit.reuseNum++
		}
		unit.cache.Add(fileBlock, BlockSize)
	}
	// 添加最后一个块
	if lastIndx == lastBlock {
		//最后一个块不完整
		s := uint32((t.m[ino].length-1)%BlockSize + 1)
		unit.cache.used += uint64(s)
		fileBlock := fileBlockPair{ino, lastIndx}
		if _, exists := unit.reuseWindow.m[fileBlock]; exists {
			unit.reuseNum++
		}
		unit.cache.Add(fileBlock, s)
	} else {
		// 最后一个块完整
		unit.cache.used += BlockSize
		fileBlock := fileBlockPair{ino, lastIndx}
		if _, exists := unit.reuseWindow.m[fileBlock]; exists {
			unit.reuseNum++
		}
		unit.cache.Add(fileBlock, BlockSize)
	}

}

// UpdateFileNumUnderDir 只更新文件编号数量
func (t *FileShadowTree) UpdateFileNumUnderDir(ic uint64, ip Ino) {
	// fs.m[ip].maxI是否存在，理论上ReadDirPlus之前
	// ReadDirPlus紧随Lookup
	dir, exists := t.m[ip]
	if !exists {
		return
	}
	if ic > dir.maxI {
		dir.maxI = ic
	}
	if ic < dir.minI {
		dir.minI = ic
	}
	dir.NumSub = dir.maxI - dir.minI
}

type fileBlockPair struct {
	ino   Ino
	block uint64
}
type entry struct {
	key   fileBlockPair
	value uint32 // 块大小
}

type LRU struct {
	t        *FileShadowTree
	ll       *list.List
	m        map[fileBlockPair]*list.Element
	used     uint64
	capacity uint64 //容量
}

// Add 添加一个值到缓存中。
// 如果键已经存在，会更新键对应的值。
// 统一从队尾删除，从队首插入
func (l *LRU) Add(key fileBlockPair, value uint32) (removedKey fileBlockPair, removed bool) {
	if ee, ok := l.m[key]; ok {
		l.ll.MoveToFront(ee)
		ee.Value.(*entry).value = value
		return fileBlockPair{0, 0}, false // 没有元素被移除，返回特定字符串和false
	}
	ele := l.ll.PushFront(&entry{key, value})
	l.m[key] = ele
	if l.used > l.capacity {
		e := l.ll.Back()
		if e != nil {
			l.ll.Remove(ele)
			kv := e.Value.(*entry)
			delete(l.m, kv.key)
			// 手动释放一次缓存
			l.t.manuallyRemove(kv.key.ino, kv.key.block*BlockSize, kv.value)
			return kv.key, true // 返回被移除元素的 key 和 true
		}
	}
	return fileBlockPair{0, 0}, false // 没有元素被移除，返回特定字符串和false
}

// CacheUnit 表示缓存单元。
type CacheUnit struct {
	ratioRecorder []float64
	node          *FileShadowNode
	nrFileTotal   uint64
	nrDirTotal    uint64 //目录数，如果有
	cacheSize     uint64
	cache         LRU //维护缓存项，到LRU的映射
	windowSize    int
	accessWindow  []uint64
	pattern       rune
	reuseWindow   LRU //维护重用项
	reuseNum      int
	marginBenefit float64
	prefixPath    string
	tree          *FileShadowTree
	nrAccess      uint64 //用于辅助本轮计算的访问块数目
	nrHit         int
	nrMiss        int
	isHighLevel   bool                       // 是否是管理多个目录的更高级目录
	dirMap        map[*FileShadowNode]uint64 // 目录编映射，如果有
}

func NewCacheUnit(node *FileShadowNode, tree *FileShadowTree) *CacheUnit {
	u := &CacheUnit{
		tree:         tree,
		node:         node,
		cacheSize:    6144, //待定值, 可以在配置中读取后计算获得
		windowSize:   30,
		pattern:      'u',
		accessWindow: make([]uint64, 0),
		reuseWindow: LRU{
			ll: list.New(),
			m:  make(map[fileBlockPair]*list.Element),
		},
		reuseNum:    0,
		nrAccess:    0,
		nrHit:       0,
		nrMiss:      0,
		isHighLevel: false,
		dirMap:      make(map[*FileShadowNode]uint64),
	}
	u.cache.ll = list.New()
	u.cache.m = make(map[fileBlockPair]*list.Element)
	u.cache.used = 0
	u.cache.capacity = u.cacheSize
	u.cache.t = nil
	u.reuseWindow.ll = list.New()
	u.reuseWindow.m = make(map[fileBlockPair]*list.Element)
	u.reuseWindow.used = 0
	u.reuseWindow.capacity = 0 // 为判断访问模式时没有reuseWindow

	return u
}

// updateInformation 更新目录相关信息
func (u *CacheUnit) updateInformation() {
	node := u.node
	for index, n := range node.childList {
		// 更新目录编号表
		u.dirMap[n] = uint64(index)
		// 更新总文件数量
		u.nrFileTotal += n.NumSub
	}

}

func (u *CacheUnit) JudgeIfStridePattern(window []uint64) bool {
	size := len(window)
	if size < 3 {
		return false
	}
	flag := true
	difference := make([]int, 0)
	for i := size - 1; i >= size-3; i-- {
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

func (u *CacheUnit) CalculateGapDistributionGaussian(window []uint64) Pair {
	var avg, std, nrSample float64
	const defaultStd, minStd = 10.0, 3.0
	size := len(window)

	for i := size - 1; i >= size-10; i-- {
		oldAvg, oldStd := avg, std
		gap := math.Abs(float64(window[i] - window[i-1]))
		var newAvg, newStd float64
		if nrSample == 0 {
			newAvg = gap
			newStd = defaultStd
		} else {
			newAvg = (oldAvg*nrSample + gap) / (nrSample + 1)
			newStd = math.Sqrt((nrSample*(math.Pow(oldStd, 2)+math.Pow(newAvg-oldAvg, 2)) + math.Pow(newAvg-gap, 2)) / (nrSample + 1))
			newStd = math.Max(newStd, minStd)
		}
		avg, std = newAvg, newStd
		nrSample++
	}
	return Pair{avg, std}
}

func (u *CacheUnit) JudgeDistribution(p Pair) bool {
	// 假定 nrFileTotal 是 CacheUnit 的一个字段
	if p.First > float64(u.nrFileTotal)*0.30 && p.First < float64(u.nrFileTotal)*0.40 {
		return true
	}
	return false
}

func (u *CacheUnit) JudgeIfRandomPattern(window []uint64) bool {
	size := len(window)
	if size < 10 {
		return false
	}
	p := u.CalculateGapDistributionGaussian(window)
	return u.JudgeDistribution(p)
}

func (u *CacheUnit) JudgeThePattern() {
	if len(u.accessWindow) < LeastLengthToJudge {
		return
	}

	if u.JudgeIfStridePattern(u.accessWindow) {
		u.pattern = 's'
		// TODO:模式切换reuseWindow是否要激活
		// u.reuseWindow.ll = nil
		return
	}

	if u.JudgeIfRandomPattern(u.accessWindow) {
		u.pattern = 'r'
		// u.reuseWindow.ll = nil
		return
	}

	// 默认为 't'（Traditional Pattern）
	u.pattern = 't'
	u.reuseWindow.ll = list.New()
	u.reuseWindow.m = make(map[fileBlockPair]*list.Element)
	u.reuseWindow.used = 0
	u.reuseNum = 0
}

func (u *CacheUnit) CalculateMarginBenefit() {
	switch u.pattern {
	case 's':
		// 人为规定一个很低的值, -1 代表不能产生收益
		u.marginBenefit = -1

	case 'r':
		// 根据数据集大小估计块数量
		// 估计块数量，计算命中率
		counter := 0
		blockNum := uint64(0)
		tmpSum := uint64(0) // 为了计算块的平均大小
		for e := u.cache.ll.Front(); e != nil && counter < 10; e = e.Next() {
			ino := e.Value.(*entry).key.ino
			l := u.tree.m[ino].length
			blockNum += (l-1)/BlockSize + 1
			tmpSum += l
			counter++
		}
		// 估计块总数
		blockSum := u.nrFileTotal / 10 * blockNum
		avgBlockSize := tmpSum / blockSum
		u.marginBenefit = 1 / float64(blockSum) * float64(u.nrAccess) / float64(avgBlockSize) // 计算期望的缓存命中数

	case 't':
		u.marginBenefit = (float64(u.reuseNum)) / float64(CapacityToTune) // 计算期望的缓存命中数
		u.reuseWindow.ll.Init()
		u.reuseWindow.m = make(map[fileBlockPair]*list.Element)
		u.reuseWindow.used = 0
		u.reuseNum = 0
	}
}

func (u *CacheUnit) TuneCapacityAndFree(goalSize uint64) {
	// 如果是扩容，直接更新 cacheSize 和 windowSize
	if goalSize > u.cacheSize {
		u.cacheSize = goalSize
		return
	}

	// 需要释放缓存缓存大小
	var capacityToFree uint64
	if u.cache.used < goalSize {
		capacityToFree = 0
	} else {
		capacityToFree = u.cache.used - goalSize
	}

	// 释放 virtualCache 头部的元素
	for capacityToFree > 0 {
		e := u.cache.ll.Back()
		if e != nil {
			toFree := e.Value.(*entry).key
			i := toFree.ino
			b := toFree.block
			length := u.tree.m[i].length
			lastBlock := (length - 1) / BlockSize
			var free uint32
			if b == lastBlock {
				free = uint32(length % BlockSize)
			} else {
				free = BlockSize
			}
			u.tree.manuallyRemove(i, b*BlockSize, free)
			u.cache.used -= uint64(free)
			u.cache.ll.Remove(e)
		}
	}

	u.cacheSize = goalSize
}
