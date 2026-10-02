// Package solver 把模拟同步调用链的时钟校正问题化为差分约束，
// 求按服务 ID 字典序最小的可行整数偏移向量；无解时给出由真实输入
// 约束构成的矛盾环证据。
package solver

import (
	"fmt"
	"math"
	"sort"
)

const (
	MinServices = 2
	MaxServices = 8
	MaxSpans    = 100
)

// maxAbs 限制输入整数量级，避免差分约束图上路径权重求和溢出。
const maxAbs = 1_000_000_000

// ZeroLabel 是矛盾环中辅助零点节点（校正时刻 0 的基准）的标签。
const ZeroLabel = "@zero"

// inf 是最短路计算使用的“无穷大”，取 MaxInt64/4 保证加法不溢出。
const inf = int64(math.MaxInt64) / 4

type Service struct {
	ID string `json:"id"`
	Lo int    `json:"lo"`
	Hi int    `json:"hi"`
}

type Span struct {
	ID      string `json:"id"`
	Service string `json:"service"`
	Parent  string `json:"parent"` // 空串表示根 span
	Start   int    `json:"start"`
	End     int    `json:"end"`
}

type Input struct {
	Services     []Service           `json:"services"`
	Spans        []Span              `json:"spans"`
	Observations []OffsetObservation `json:"observations,omitempty"`
}

// OffsetObservation 是两端事件之间实测经过时间的整数区间约束：
//
//	min <= 校正后(later 事件) - 校正后(earlier 事件) <= max
//
// 每一端要么是某个服务的时钟基准点（原始时刻 0，用 Earlier/Later 指定
// 服务），要么是某个 span 的起点/终点（用 EarlierSpan+EarlierPoint 指定，
// 服务由该 span 决定）。两端可位于同一服务，也可混用两种端点。
type OffsetObservation struct {
	ID           string `json:"id"`
	Earlier      string `json:"earlier,omitempty"`
	Later        string `json:"later,omitempty"`
	EarlierSpan  string `json:"earlierSpan,omitempty"`
	LaterSpan    string `json:"laterSpan,omitempty"`
	EarlierPoint string `json:"earlierPoint,omitempty"` // start | end
	LaterPoint   string `json:"laterPoint,omitempty"`   // start | end
	Min          int    `json:"min"`
	Max          int    `json:"max"`
}

// EdgeKind 标记一条差分约束边的来源。
type EdgeKind string

const (
	KindBoundUpper     EdgeKind = "bound_upper" // x_i <= hi
	KindBoundLower     EdgeKind = "bound_lower" // x_i >= lo
	KindChildStart     EdgeKind = "child_start" // 子调用起点不早于父调用起点
	KindChildEnd       EdgeKind = "child_end"   // 子调用终点不晚于父调用终点
	KindObservationMin EdgeKind = "observation_min"
	KindObservationMax EdgeKind = "observation_max"
)

// EdgeRef 记录一条约束边对应的原始输入，用于把矛盾环还原成证据。
type EdgeRef struct {
	Kind        EdgeKind `json:"kind"`
	Service     string   `json:"service,omitempty"`
	Span        string   `json:"span,omitempty"`
	ParentSpan  string   `json:"parentSpan,omitempty"`
	Observation string   `json:"observation,omitempty"`
}

// edge 是约束图中的一条边：x[to] - x[from] <= w。节点 0 是固定为 0 的
// 辅助变量，服务 i 对应节点 i+1（按服务 ID 排序）。
type edge struct {
	from, to int
	w        int
	ref      EdgeRef
}

// Validate 校验输入，返回全部问题（为空表示合法）。
func Validate(in Input) []string {
	var errs []string
	add := func(format string, args ...any) {
		errs = append(errs, fmt.Sprintf(format, args...))
	}
	if len(in.Services) < MinServices || len(in.Services) > MaxServices {
		add("服务数量必须在 %d..%d 之间，当前为 %d", MinServices, MaxServices, len(in.Services))
	}
	seenSvc := map[string]bool{}
	anchors := 0
	for _, s := range in.Services {
		if s.ID == "" {
			add("服务 ID 不能为空")
			continue
		}
		if seenSvc[s.ID] {
			add("服务 ID %q 重复", s.ID)
		}
		seenSvc[s.ID] = true
		if s.Lo > s.Hi {
			add("服务 %s 的偏移下界 %d 大于上界 %d", s.ID, s.Lo, s.Hi)
		}
		if absExceeds(s.Lo) || absExceeds(s.Hi) {
			add("服务 %s 的偏移界超出允许范围 ±%d", s.ID, maxAbs)
		}
		if s.Lo == 0 && s.Hi == 0 {
			anchors++
		}
	}
	if anchors != 1 {
		add("必须恰好有一个锚定服务（偏移区间 [0,0]），当前 %d 个", anchors)
	}
	if len(in.Spans) > MaxSpans {
		add("span 数量至多为 %d，当前 %d", MaxSpans, len(in.Spans))
	}
	byID := map[string]Span{}
	for _, sp := range in.Spans {
		if sp.ID == "" {
			add("span ID 不能为空")
			continue
		}
		if _, dup := byID[sp.ID]; dup {
			add("span ID %q 重复", sp.ID)
		}
		byID[sp.ID] = sp
		if !seenSvc[sp.Service] {
			add("span %s 引用了未知服务 %q", sp.ID, sp.Service)
		}
		if sp.Start > sp.End {
			add("span %s 的开始时刻 %d 晚于结束时刻 %d", sp.ID, sp.Start, sp.End)
		}
		if absExceeds(sp.Start) || absExceeds(sp.End) {
			add("span %s 的时刻超出允许范围 ±%d", sp.ID, maxAbs)
		}
	}
	for _, sp := range in.Spans {
		if sp.Parent == "" {
			continue
		}
		if _, ok := byID[sp.Parent]; !ok {
			add("span %s 的父 span %q 不存在", sp.ID, sp.Parent)
			continue
		}
		// 沿父链检查环。
		seen := map[string]bool{sp.ID: true}
		for cur := sp.Parent; cur != ""; {
			if seen[cur] {
				add("span %s 的父链存在环（经过 %s）", sp.ID, cur)
				break
			}
			seen[cur] = true
			cur = byID[cur].Parent
		}
	}
	seenObservation := map[string]bool{}
	for _, obs := range in.Observations {
		if obs.ID == "" || seenObservation[obs.ID] {
			add("观测 ID 为空或重复: %q", obs.ID)
		}
		seenObservation[obs.ID] = true
		eSvc, eOK := resolveObsRef(obs.Earlier, obs.EarlierSpan, obs.EarlierPoint, seenSvc, byID)
		lSvc, lOK := resolveObsRef(obs.Later, obs.LaterSpan, obs.LaterPoint, seenSvc, byID)
		if !eOK {
			add("观测 %s 的起始端无效（须指定存在的服务，或存在的 span 加 start/end 端点）", obs.ID)
		}
		if !lOK {
			add("观测 %s 的结束端无效（须指定存在的服务，或存在的 span 加 start/end 端点）", obs.ID)
		}
		// 仅当两端都是服务基准点时，同一服务才无意义（两端点事件允许同服务）。
		if eOK && lOK && obs.EarlierSpan == "" && obs.LaterSpan == "" && eSvc == lSvc {
			add("观测 %s 的两个基准点落在同一服务上，不构成服务间约束", obs.ID)
		}
		if obs.Min > obs.Max || absExceeds(obs.Min) || absExceeds(obs.Max) {
			add("观测 %s 的区间无效", obs.ID)
		}
	}
	return errs
}

// resolveObsRef 解析观测一端，返回该端所在服务 ID。spanID 非空时为该 span
// 的起点/终点（服务由 span 决定）；否则为 svcID 指向的时钟基准点。
func resolveObsRef(svcID, spanID, point string, seenSvc map[string]bool, byID map[string]Span) (string, bool) {
	if spanID != "" {
		sp, ok := byID[spanID]
		if !ok || (point != "start" && point != "end") {
			return "", false
		}
		return sp.Service, true
	}
	if !seenSvc[svcID] {
		return "", false
	}
	return svcID, true
}

func absExceeds(v int) bool {
	return v > maxAbs || v < -maxAbs
}

// CorrectedSpan 是带上校正时刻的 span，直接用于绘制时间线。
type CorrectedSpan struct {
	ID             string `json:"id"`
	Service        string `json:"service"`
	Parent         string `json:"parent"`
	Start          int    `json:"start"`
	End            int    `json:"end"`
	CorrectedStart int    `json:"correctedStart"`
	CorrectedEnd   int    `json:"correctedEnd"`
}

// ConstraintSlack 是一条父子约束在校正后的余量（均须 >= 0）。
type ConstraintSlack struct {
	Span       string `json:"span"`
	ParentSpan string `json:"parentSpan"`
	StartSlack int    `json:"startSlack"`
	EndSlack   int    `json:"endSlack"`
}

// CycleEdge 是矛盾环中的一条边，From/To 为服务 ID 或 ZeroLabel。
type CycleEdge struct {
	From   string  `json:"from"`
	To     string  `json:"to"`
	Weight int     `json:"weight"`
	Ref    EdgeRef `json:"ref"`
}

// Cycle 是无解证据：一组首尾相接、总权重为负的真实约束边。
type Cycle struct {
	TotalWeight int         `json:"totalWeight"`
	Edges       []CycleEdge `json:"edges"`
}

// Result 是求解响应。Status 为 "ok" 或 "infeasible"；两者互斥地携带
// 校正结果或矛盾环，绝不会同时出现。
type Result struct {
	Status       string             `json:"status"`
	Order        []string           `json:"order,omitempty"`
	Offsets      map[string]int     `json:"offsets,omitempty"`
	Spans        []CorrectedSpan    `json:"spans,omitempty"`
	Constraints  []ConstraintSlack  `json:"constraints,omitempty"`
	Cycle        *Cycle             `json:"cycle,omitempty"`
	Observations []ObservationSlack `json:"observations,omitempty"`
}

type ObservationSlack struct {
	ID               string `json:"id"`
	Difference       int    `json:"difference"`
	CorrectedEarlier int    `json:"correctedEarlier"`
	CorrectedLater   int    `json:"correctedLater"`
	MinSlack         int    `json:"minSlack"`
	MaxSlack         int    `json:"maxSlack"`
}

// buildGraph 把输入化为差分约束图。
//
// 记 x[s] 为服务 s 的时钟偏移，则：
//   - 偏移界 lo<=x[s]<=hi 化为 0->s (权 hi) 与 s->0 (权 -lo)；
//   - 子调用完整落在父调用内：
//     c.start+x[cs] >= p.start+x[ps]  <=>  x[ps]-x[cs] <= c.start-p.start
//     c.end  +x[cs] <= p.end  +x[ps]  <=>  x[cs]-x[ps] <= p.end-c.end
func buildGraph(in Input) (n int, idx map[string]int, order []string, edges []edge) {
	order = make([]string, 0, len(in.Services))
	svc := make(map[string]Service, len(in.Services))
	for _, s := range in.Services {
		order = append(order, s.ID)
		svc[s.ID] = s
	}
	sort.Strings(order)
	idx = make(map[string]int, len(order))
	for i, id := range order {
		idx[id] = i + 1
	}
	n = len(order) + 1

	for _, id := range order {
		s := svc[id]
		edges = append(edges,
			edge{from: 0, to: idx[id], w: s.Hi, ref: EdgeRef{Kind: KindBoundUpper, Service: id}},
			edge{from: idx[id], to: 0, w: -s.Lo, ref: EdgeRef{Kind: KindBoundLower, Service: id}},
		)
	}
	spans := make(map[string]Span, len(in.Spans))
	for _, sp := range in.Spans {
		spans[sp.ID] = sp
	}
	for _, sp := range in.Spans {
		if sp.Parent == "" {
			continue
		}
		p := spans[sp.Parent]
		cs, ps := idx[sp.Service], idx[p.Service]
		edges = append(edges,
			edge{from: cs, to: ps, w: sp.Start - p.Start, ref: EdgeRef{Kind: KindChildStart, Span: sp.ID, ParentSpan: p.ID}},
			edge{from: ps, to: cs, w: p.End - sp.End, ref: EdgeRef{Kind: KindChildEnd, Span: sp.ID, ParentSpan: p.ID}},
		)
	}
	for _, obs := range in.Observations {
		e := resolveObsEvent(obs.Earlier, obs.EarlierSpan, obs.EarlierPoint, idx, spans)
		l := resolveObsEvent(obs.Later, obs.LaterSpan, obs.LaterPoint, idx, spans)
		// 边 u->v (权 w) 表示 x[v]-x[u] <= w；d = (t_l+x[l])-(t_e+x[e])。
		// d <= max  <=>  x[l]-x[e] <= max-t_l+t_e   => 边 e->l
		// d >= min  <=>  x[e]-x[l] <= t_l-t_e-min   => 边 l->e
		edges = append(edges,
			edge{from: e.node, to: l.node, w: obs.Max - l.t + e.t,
				ref: EdgeRef{Kind: KindObservationMax, Observation: obs.ID}},
			edge{from: l.node, to: e.node, w: l.t - e.t - obs.Min,
				ref: EdgeRef{Kind: KindObservationMin, Observation: obs.ID}},
		)
	}
	return n, idx, order, edges
}

// obsEvent 是观测一端解析后的事件：节点 node 的时钟上、本地时刻 t 的点
// （服务基准点对应 t=0）。
type obsEvent struct {
	node int
	t    int
}

// resolveObsEvent 把观测的一端解析为 (图节点, 本地时刻)。spanID 非空时
// 为该 span 的起点/终点，否则为服务 svcID 的时钟基准点（t=0）。
func resolveObsEvent(svcID, spanID, point string, idx map[string]int, spans map[string]Span) obsEvent {
	if spanID != "" {
		sp := spans[spanID]
		if point == "end" {
			return obsEvent{node: idx[sp.Service], t: sp.End}
		}
		return obsEvent{node: idx[sp.Service], t: sp.Start}
	}
	return obsEvent{node: idx[svcID], t: 0}
}

// negativeCycle 用 Bellman-Ford 检测负环；所有节点距离初始化为 0，
// 等价于挂了一个虚拟超级源，因此能发现图中任意负环。
func negativeCycle(n int, edges []edge) ([]edge, bool) {
	dist := make([]int64, n)
	parent := make([]int, n)
	for i := range parent {
		parent[i] = -1
	}
	updated := -1
	for iter := 0; iter < n; iter++ {
		updated = -1
		for ei, e := range edges {
			if dist[e.from]+int64(e.w) < dist[e.to] {
				dist[e.to] = dist[e.from] + int64(e.w)
				parent[e.to] = ei
				updated = e.to
			}
		}
	}
	if updated == -1 {
		return nil, false
	}
	// 第 n 轮仍能松弛，说明 updated 受负环影响；沿父指针走 n 步必入环。
	v := updated
	for i := 0; i < n; i++ {
		pe := parent[v]
		if pe < 0 {
			return nil, false // 防御：理论上不可达
		}
		v = edges[pe].from
	}
	var cyc []edge
	sum := 0
	for cur := v; ; {
		pe := parent[cur]
		if pe < 0 {
			return nil, false // 防御：理论上不可达
		}
		e := edges[pe]
		cyc = append([]edge{e}, cyc...) // 前插，得到正向环
		sum += e.w
		cur = e.from
		if cur == v {
			break
		}
	}
	if sum >= 0 {
		return nil, false // 防御：理论上不可达
	}
	return cyc, true
}

// floydWarshall 求全源最短路，调用前须确认无负环。
func floydWarshall(n int, edges []edge) [][]int64 {
	d := make([][]int64, n)
	for i := range d {
		d[i] = make([]int64, n)
		for j := range d[i] {
			d[i][j] = inf
		}
		d[i][i] = 0
	}
	for _, e := range edges {
		if int64(e.w) < d[e.from][e.to] {
			d[e.from][e.to] = int64(e.w)
		}
	}
	for k := 0; k < n; k++ {
		for i := 0; i < n; i++ {
			if d[i][k] >= inf/2 {
				continue
			}
			for j := 0; j < n; j++ {
				if nd := d[i][k] + d[k][j]; nd < d[i][j] {
					d[i][j] = nd
				}
			}
		}
	}
	return d
}

// Solve 求解。输入须先通过 Validate。
//
// 字典序最小解的构造：按服务 ID 顺序逐个固定变量。固定 x_j=v_j 等价于
// 加入边 j->0（权 -v_j），于是在已固定集合 F 下 x_k 的最小可行值为
// max_{j in F∪{0}} (v_j - dist(k,j))，其中 dist 为原图最短路。差分约束
// 系统单变量可行值构成区间，取到最小值后系统仍可满足，故贪心成立。
func Solve(in Input) (Result, error) {
	n, idx, order, edges := buildGraph(in)

	if cyc, ok := negativeCycle(n, edges); ok {
		cycle := &Cycle{}
		for _, e := range cyc {
			cycle.Edges = append(cycle.Edges, CycleEdge{
				From:   nodeLabel(e.from, order),
				To:     nodeLabel(e.to, order),
				Weight: e.w,
				Ref:    e.ref,
			})
			cycle.TotalWeight += e.w
		}
		if cycle.TotalWeight >= 0 {
			return Result{}, fmt.Errorf("内部错误：矛盾环总权重非负（%d）", cycle.TotalWeight)
		}
		return Result{Status: "infeasible", Cycle: cycle}, nil
	}

	dist := floydWarshall(n, edges)
	values := make([]int64, n) // 节点 0 固定为 0
	fixed := []int{0}
	for _, id := range order {
		k := idx[id]
		best := int64(math.MinInt64)
		for _, j := range fixed {
			if dist[k][j] >= inf/2 {
				continue
			}
			if cand := values[j] - dist[k][j]; cand > best {
				best = cand
			}
		}
		if best == int64(math.MinInt64) {
			return Result{}, fmt.Errorf("内部错误：服务 %s 没有可行下界", id)
		}
		values[k] = best
		fixed = append(fixed, k)
	}
	// 防御性复核：求得的偏移必须满足全部约束。
	for _, e := range edges {
		if values[e.to] > values[e.from]+int64(e.w) {
			return Result{}, fmt.Errorf("内部错误：偏移结果违反约束 %s", e.ref.Kind)
		}
	}

	res := Result{Status: "ok", Order: order, Offsets: make(map[string]int, len(order))}
	for _, id := range order {
		res.Offsets[id] = int(values[idx[id]])
	}
	spans := make(map[string]Span, len(in.Spans))
	for _, sp := range in.Spans {
		spans[sp.ID] = sp
	}
	for _, sp := range in.Spans {
		off := res.Offsets[sp.Service]
		res.Spans = append(res.Spans, CorrectedSpan{
			ID: sp.ID, Service: sp.Service, Parent: sp.Parent,
			Start: sp.Start, End: sp.End,
			CorrectedStart: sp.Start + off, CorrectedEnd: sp.End + off,
		})
		if sp.Parent == "" {
			continue
		}
		p := spans[sp.Parent]
		poff := res.Offsets[p.Service]
		res.Constraints = append(res.Constraints, ConstraintSlack{
			Span:       sp.ID,
			ParentSpan: p.ID,
			StartSlack: (sp.Start + off) - (p.Start + poff),
			EndSlack:   (p.End + poff) - (sp.End + off),
		})
	}
	for _, obs := range in.Observations {
		e := resolveObsEvent(obs.Earlier, obs.EarlierSpan, obs.EarlierPoint, idx, spans)
		l := resolveObsEvent(obs.Later, obs.LaterSpan, obs.LaterPoint, idx, spans)
		correctedEarlier := e.t + int(values[e.node])
		correctedLater := l.t + int(values[l.node])
		difference := correctedLater - correctedEarlier
		res.Observations = append(res.Observations, ObservationSlack{
			ID: obs.ID, Difference: difference,
			CorrectedEarlier: correctedEarlier, CorrectedLater: correctedLater,
			MinSlack: difference - obs.Min, MaxSlack: obs.Max - difference,
		})
	}
	return res, nil
}

func nodeLabel(node int, order []string) string {
	if node == 0 {
		return ZeroLabel
	}
	return order[node-1]
}
