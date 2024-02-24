package fuse

import (
	"container/list"
	"fmt"
	"github.com/hanwen/go-fuse/v2/fuse"
	"math"
	"os"
	"sort"
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
	childList        []Ino
	inode            Ino //对应的Inode
	isManagementNode bool
	isOpen           bool
	frange           []Range
	length           uint64 // 主要记录文件数量
}

func NewFileShadowNode(p string, i Ino, f *FileShadowNode) *FileShadowNode {
	return &FileShadowNode{
		pathName:         p,
		father:           f,
		NumSub:           0, // 次级目录文件总数
		maxI:             0,
		minI:             math.MaxInt64,
		childList:        make([]Ino, 0),
		inode:            i,
		isManagementNode: false,
		isOpen:           false,
		frange:           make([]Range, 0),
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
	lastLevelDirNode   []*FileShadowNode
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
		lastLevelDirNode: make([]*FileShadowNode, 0),
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

// GenerateNode 根据fuse.Lookup的分解生成节点建树，使用Inod没有重名冲突
func (t *FileShadowTree) GenerateNode(name string, ip Ino, ic Ino) {
	// TODO: 更新时间以及根据时间剪枝
	// 如果已经生成
	fmt.Println(ic)
	// 孩子节点已经存在或该节点的父母不存在，则不需要建立新节点
	_, exists := t.m[ic]
	if exists {
		return
	}
	parent, exists := t.m[ip]
	if !exists {
		return
	}
	// 建立父节点和子节点关系
	node := NewFileShadowNode(name, ic, parent)
	parent.childList = append(t.m[ip].childList, ic)
	// inode到节点映射
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
	rin.NodeId = uint64(ino) //换成实际要释放的NodeId
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
	for _, n := range t.lastLevelDirNode {
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

// processOpenFileAttr 根据fuse.Open打开文件进行处理
func (t *FileShadowTree) processOpenFileAttr(i Ino, attr *Attr) {
	n, exists := t.m[i]
	if !exists {
		return
	}
	t.accessNum++
	if t.accessNum%200 == 0 {
		t.TuneCacheCapacity()
	}
	n.isOpen = true
	t.m[i].length = attr.Length // 记录一个文件的大小
	s := t.m[i].father
	t.m[i].cacheUnitNode = s // 暂时认为缓存管理由其father进行
	cacheUnit, exists := t.nodeToCache[s]
	if exists {
		cacheUnit.accessWindow = append(cacheUnit.accessWindow, i)
		if len(cacheUnit.accessWindow) > accessWindowSize {
			cacheUnit.accessWindow = cacheUnit.accessWindow[1:]
		}
		return
	}

	s.isManagementNode = true
	// 记录最后一级目录节点，作为缓存管理的单位
	t.lastLevelDirNode = append(t.lastLevelDirNode, s)
	// 构造一个CacheUnit，和最后一层目录产生映射
	// 构造时传入node，可以访问node的所有信息
	c := NewCacheUnit(s, t)
	c.nrFileTotal = s.NumSub //获得目录下文件总数
	t.nodeToCache[s] = c
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
	cacheSize     uint64
	cache         LRU //维护缓存项，到LRU的映射
	windowSize    int
	accessWindow  []Ino
	pattern       rune
	reuseWindow   LRU //维护重用项
	reuseNum      int
	marginBenefit float64
	prefixPath    string
	tree          *FileShadowTree
	nrAccess      uint64 //用于辅助本轮计算的访问块数目
	nrHit         int
	nrMiss        int
}

func NewCacheUnit(node *FileShadowNode, tree *FileShadowTree) *CacheUnit {
	u := &CacheUnit{
		tree:         tree,
		node:         node,
		cacheSize:    6144, //待定值
		windowSize:   30,
		pattern:      'u',
		accessWindow: make([]Ino, 0),
		reuseWindow: LRU{
			ll: list.New(),
			m:  make(map[fileBlockPair]*list.Element),
		},
		reuseNum: 0,
		nrAccess: 0,
		nrHit:    0,
		nrMiss:   0,
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

func (u *CacheUnit) JudgeIfStridePattern(window []Ino) bool {
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

func (u *CacheUnit) CalculateGapDistributionGaussian(window []Ino) Pair {
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

func (u *CacheUnit) JudgeIfRandomPattern(window []Ino) bool {
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
	if uint64(u.cache.used) < goalSize {
		capacityToFree = 0
	} else {
		capacityToFree = uint64(u.cache.used) - goalSize
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
