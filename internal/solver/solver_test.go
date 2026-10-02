package solver

import (
	"math/rand"
	"sort"
	"testing"
)

// ---------- 穷举对拍 ----------

// bruteForceLexMin 穷举所有界内整数偏移向量，返回字典序最小可行解。
func bruteForceLexMin(in Input) ([]int, bool) {
	_, _, order, _ := buildGraph(in)
	svc := map[string]Service{}
	for _, s := range in.Services {
		svc[s.ID] = s
	}
	var best []int
	cur := make([]int, len(order))
	var rec func(i int)
	rec = func(i int) {
		if i == len(order) {
			if feasibleVec(in, order, cur) && (best == nil || lexLess(cur, best)) {
				best = append([]int(nil), cur...)
			}
			return
		}
		s := svc[order[i]]
		for v := s.Lo; v <= s.Hi; v++ {
			cur[i] = v
			rec(i + 1)
		}
	}
	rec(0)
	return best, best != nil
}

func feasibleVec(in Input, order []string, vec []int) bool {
	off := make(map[string]int, len(order))
	for i, id := range order {
		off[id] = vec[i]
	}
	spans := map[string]Span{}
	for _, sp := range in.Spans {
		spans[sp.ID] = sp
	}
	for _, sp := range in.Spans {
		if sp.Parent == "" {
			continue
		}
		p := spans[sp.Parent]
		if sp.Start+off[sp.Service] < p.Start+off[p.Service] {
			return false
		}
		if sp.End+off[sp.Service] > p.End+off[p.Service] {
			return false
		}
	}
	for _, obs := range in.Observations {
		earlierSvc, laterSvc, delta := observationEndpoints(obs, spans)
		diff := off[laterSvc] - off[earlierSvc] + delta
		if diff < obs.Min || diff > obs.Max {
			return false
		}
	}
	return true
}

func lexLess(a, b []int) bool {
	for i := range a {
		if a[i] != b[i] {
			return a[i] < b[i]
		}
	}
	return false
}

// randInput 生成小规模随机输入：2~3 个服务（恰一个锚定）、1~6 个
// 构成森林的 span、窄偏移区间，保证穷举可行。
func randInput(r *rand.Rand) Input {
	nSvc := 2 + r.Intn(2)
	anchor := r.Intn(nSvc)
	in := Input{}
	for i := 0; i < nSvc; i++ {
		id := string(rune('a' + i))
		if i == anchor {
			in.Services = append(in.Services, Service{ID: id, Lo: 0, Hi: 0})
			continue
		}
		lo := -3 + r.Intn(6) // [-3,2]
		hi := lo + r.Intn(7-lo)
		if lo == 0 && hi == 0 {
			hi = 1 // 非锚定服务不得恰好是 [0,0]
		}
		in.Services = append(in.Services, Service{ID: id, Lo: lo, Hi: hi})
	}
	nSpans := 1 + r.Intn(6)
	for i := 0; i < nSpans; i++ {
		sp := Span{
			ID:      "s" + string(rune('0'+i)),
			Service: in.Services[r.Intn(nSvc)].ID,
			Start:   -6 + r.Intn(13),
		}
		sp.End = sp.Start + r.Intn(7)
		if i > 0 && r.Intn(4) > 0 {
			sp.Parent = in.Spans[r.Intn(i)].ID
		}
		in.Spans = append(in.Spans, sp)
	}
	// 随机附加 0~3 条观测：服务间或 span 起止端点（时刻可为负、两端可
	// 落在同一服务，且观测之间/观测与调用链可能真正冲突——可行性结论
	// 与字典序最小解都由穷举对拍保证）。
	for i := 0; i < r.Intn(4); i++ {
		obs := OffsetObservation{ID: "o" + string(rune('0'+i))}
		obs.Min = -6 + r.Intn(13)
		obs.Max = obs.Min + r.Intn(13)
		if r.Intn(2) == 0 {
			obs.EarlierSpan = in.Spans[r.Intn(len(in.Spans))].ID
			obs.LaterSpan = in.Spans[r.Intn(len(in.Spans))].ID
			obs.EarlierPoint = []string{"start", "end"}[r.Intn(2)]
			obs.LaterPoint = []string{"start", "end"}[r.Intn(2)]
		} else {
			a, b := r.Intn(nSvc), r.Intn(nSvc-1)
			if b >= a {
				b++
			}
			obs.Earlier = in.Services[a].ID
			obs.Later = in.Services[b].ID
		}
		in.Observations = append(in.Observations, obs)
	}
	return in
}

func TestSolveAgainstBruteForce(t *testing.T) {
	const iterations = 4000
	for seed := int64(0); seed < iterations; seed++ {
		r := rand.New(rand.NewSource(seed))
		in := randInput(r)
		if errs := Validate(in); len(errs) != 0 {
			t.Fatalf("seed %d: 生成器产生了非法输入: %v", seed, errs)
		}
		res, err := Solve(in)
		if err != nil {
			t.Fatalf("seed %d: Solve 返回错误: %v", seed, err)
		}
		best, ok := bruteForceLexMin(in)
		if ok != (res.Status == "ok") {
			t.Fatalf("seed %d: 可行性不一致 solver=%s brute=%v\n输入: %+v", seed, res.Status, ok, in)
		}
		if !ok {
			checkCycleEvidence(t, in, res.Cycle)
			continue
		}
		_, _, order, _ := buildGraph(in)
		for i, id := range order {
			if res.Offsets[id] != best[i] {
				t.Fatalf("seed %d: 字典序最小解不一致\nsolver=%v\nbrute =%v\n输入: %+v",
					seed, res.Offsets, best, in)
			}
		}
		checkSlacks(t, in, res)
	}
}

// ---------- 余量复核 ----------

func checkSlacks(t *testing.T, in Input, res Result) {
	t.Helper()
	spans := map[string]Span{}
	for _, sp := range in.Spans {
		spans[sp.ID] = sp
	}
	seen := map[string]bool{}
	for _, c := range res.Constraints {
		sp := spans[c.Span]
		p := spans[c.ParentSpan]
		if sp.ID == "" || p.ID == "" || sp.Parent != p.ID {
			t.Fatalf("余量条目引用了不存在的父子关系: %+v", c)
		}
		seen[c.Span] = true
		wantStart := (sp.Start + res.Offsets[sp.Service]) - (p.Start + res.Offsets[p.Service])
		wantEnd := (p.End + res.Offsets[p.Service]) - (sp.End + res.Offsets[sp.Service])
		if c.StartSlack != wantStart || c.EndSlack != wantEnd {
			t.Fatalf("span %s 余量错误: got (%d,%d) want (%d,%d)",
				sp.ID, c.StartSlack, c.EndSlack, wantStart, wantEnd)
		}
		if c.StartSlack < 0 || c.EndSlack < 0 {
			t.Fatalf("span %s 余量为负: %+v", sp.ID, c)
		}
	}
	for _, sp := range in.Spans {
		if sp.Parent != "" && !seen[sp.ID] {
			t.Fatalf("缺少 span %s 的余量条目", sp.ID)
		}
	}
	obsByID := map[string]OffsetObservation{}
	for _, obs := range in.Observations {
		obsByID[obs.ID] = obs
	}
	seenObs := map[string]bool{}
	for _, o := range res.Observations {
		obs, ok := obsByID[o.ID]
		if !ok {
			t.Fatalf("观测余量引用了不存在的观测: %+v", o)
		}
		seenObs[o.ID] = true
		earlierSvc, laterSvc, delta := observationEndpoints(obs, spans)
		wantDiff := res.Offsets[laterSvc] - res.Offsets[earlierSvc] + delta
		if o.Difference != wantDiff {
			t.Fatalf("观测 %s 差值错误: got %d want %d", o.ID, o.Difference, wantDiff)
		}
		if o.MinSlack != wantDiff-obs.Min || o.MaxSlack != obs.Max-wantDiff {
			t.Fatalf("观测 %s 余量错误: got (%d,%d) want (%d,%d)",
				o.ID, o.MinSlack, o.MaxSlack, wantDiff-obs.Min, obs.Max-wantDiff)
		}
		if o.MinSlack < 0 || o.MaxSlack < 0 {
			t.Fatalf("观测 %s 余量为负: %+v", o.ID, o)
		}
	}
	for _, obs := range in.Observations {
		if !seenObs[obs.ID] {
			t.Fatalf("缺少观测 %s 的余量条目", obs.ID)
		}
	}
}

// ---------- 矛盾环逐边核验 ----------

// checkCycleEvidence 不依赖求解器内部结构，直接从原始输入独立重算每条
// 边的端点与权重，验证环确实由真实约束构成、首尾相接且总权重为负。
func checkCycleEvidence(t *testing.T, in Input, cyc *Cycle) {
	t.Helper()
	if cyc == nil {
		t.Fatal("无解但未给出矛盾环")
	}
	if len(cyc.Edges) == 0 {
		t.Fatal("矛盾环为空")
	}
	svc := map[string]Service{}
	for _, s := range in.Services {
		svc[s.ID] = s
	}
	spans := map[string]Span{}
	for _, sp := range in.Spans {
		spans[sp.ID] = sp
	}
	obsByID := map[string]OffsetObservation{}
	for _, obs := range in.Observations {
		obsByID[obs.ID] = obs
	}
	sum := 0
	for i, ce := range cyc.Edges {
		next := cyc.Edges[(i+1)%len(cyc.Edges)]
		if ce.To != next.From {
			t.Fatalf("第 %d 条边 %s->%s 与下一条 %s->%s 不相接", i, ce.From, ce.To, next.From, next.To)
		}
		sum += ce.Weight
		checkEdgeAgainstInput(t, i, ce, svc, spans, obsByID)
	}
	if sum != cyc.TotalWeight {
		t.Fatalf("环总权重不一致: 边求和=%d 报告=%d", sum, cyc.TotalWeight)
	}
	if sum >= 0 {
		t.Fatalf("矛盾环总权重必须 < 0，实际 %d", sum)
	}
}

// checkEdgeAgainstInput 按边声明的来源，从原始输入独立重算权重与端点。
func checkEdgeAgainstInput(t *testing.T, i int, ce CycleEdge, svc map[string]Service, spans map[string]Span, obsByID map[string]OffsetObservation) {
	t.Helper()
	var wantFrom, wantTo string
	var wantW int
	switch ce.Ref.Kind {
	case KindBoundUpper:
		s, ok := svc[ce.Ref.Service]
		if !ok {
			t.Fatalf("第 %d 条边引用未知服务 %q", i, ce.Ref.Service)
		}
		wantFrom, wantTo, wantW = ZeroLabel, s.ID, s.Hi
	case KindBoundLower:
		s, ok := svc[ce.Ref.Service]
		if !ok {
			t.Fatalf("第 %d 条边引用未知服务 %q", i, ce.Ref.Service)
		}
		wantFrom, wantTo, wantW = s.ID, ZeroLabel, -s.Lo
	case KindChildStart:
		sp, p := spans[ce.Ref.Span], spans[ce.Ref.ParentSpan]
		if sp.ID == "" || p.ID == "" || sp.Parent != p.ID {
			t.Fatalf("第 %d 条边引用了不存在的父子关系 %+v", i, ce.Ref)
		}
		wantFrom, wantTo, wantW = sp.Service, p.Service, sp.Start-p.Start
	case KindChildEnd:
		sp, p := spans[ce.Ref.Span], spans[ce.Ref.ParentSpan]
		if sp.ID == "" || p.ID == "" || sp.Parent != p.ID {
			t.Fatalf("第 %d 条边引用了不存在的父子关系 %+v", i, ce.Ref)
		}
		wantFrom, wantTo, wantW = p.Service, sp.Service, p.End-sp.End
	case KindObservationMax, KindObservationMin:
		obs, ok := obsByID[ce.Ref.Observation]
		if !ok {
			t.Fatalf("第 %d 条边引用未知观测 %q", i, ce.Ref.Observation)
		}
		earlierSvc, laterSvc, delta := observationEndpoints(obs, spans)
		if ce.Ref.Kind == KindObservationMax {
			wantFrom, wantTo, wantW = earlierSvc, laterSvc, obs.Max-delta
		} else {
			wantFrom, wantTo, wantW = laterSvc, earlierSvc, delta-obs.Min
		}
	default:
		t.Fatalf("第 %d 条边来源类型未知: %q", i, ce.Ref.Kind)
	}
	if ce.From != wantFrom || ce.To != wantTo || ce.Weight != wantW {
		t.Fatalf("第 %d 条边与输入不符: 环中 (%s->%s w=%d)，由输入重算 (%s->%s w=%d)",
			i, ce.From, ce.To, ce.Weight, wantFrom, wantTo, wantW)
	}
}

// ---------- 定向用例 ----------

func TestLexMinHandcrafted(t *testing.T) {
	// a 锚定；b 的区间 [-10,10]，子本地起点比父起点早 3，故 x_b >= 3。
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -10, Hi: 10}},
		Spans: []Span{
			{ID: "s1", Service: "a", Start: 0, End: 100},
			{ID: "s2", Service: "b", Parent: "s1", Start: -3, End: 0},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if res.Offsets["b"] != 3 {
		t.Fatalf("x_b 应取最小可行值 3，实际 %d", res.Offsets["b"])
	}
	// 约束去掉后应退到下界 -10。
	in.Spans = in.Spans[:1]
	res, _ = Solve(in)
	if res.Offsets["b"] != -10 {
		t.Fatalf("无约束时 x_b 应取下界 -10，实际 %d", res.Offsets["b"])
	}
}

func TestLexMinRespectsServiceOrder(t *testing.T) {
	// 字典序按服务 ID：x_aa 先最小化。窗口宽松，两服务均应取到下界。
	in := Input{
		Services: []Service{
			{ID: "aa", Lo: -5, Hi: 5},
			{ID: "mm", Lo: 0, Hi: 0},
			{ID: "zz", Lo: -5, Hi: 5},
		},
		Spans: []Span{
			{ID: "s1", Service: "mm", Start: 0, End: 100},
			{ID: "s2", Service: "aa", Parent: "s1", Start: 10, End: 20},
			{ID: "s3", Service: "zz", Parent: "s1", Start: 10, End: 20},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if res.Offsets["aa"] != -5 || res.Offsets["zz"] != -5 || res.Offsets["mm"] != 0 {
		t.Fatalf("两服务互不干扰，均应取下界: %+v", res.Offsets)
	}
	// 现在让 aa 与 zz 竞争：zz 的父是 aa 的 span，窗口与父完全等长。
	in.Spans = append(in.Spans, Span{ID: "s4", Service: "zz", Parent: "s2", Start: 10, End: 20})
	res, err = Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	// x_aa 最小化到 -5 后，zz 需满足 x_zz >= x_aa + (10-10) 且
	// x_zz <= x_aa + (20-20) => x_zz == x_aa == -5。
	if res.Offsets["aa"] != -5 || res.Offsets["zz"] != -5 {
		t.Fatalf("字典序最小应为 aa=-5, zz=-5，实际 %+v", res.Offsets)
	}
}

func TestSelfLoopInfeasible(t *testing.T) {
	// 同服务父子：本地时钟下子起点已早于父起点，无法校正。
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -5, Hi: 5}},
		Spans: []Span{
			{ID: "s1", Service: "b", Start: 10, End: 20},
			{ID: "s2", Service: "b", Parent: "s1", Start: 5, End: 15},
		},
	}
	res, err := Solve(in)
	if err != nil {
		t.Fatal(err)
	}
	if res.Status != "infeasible" {
		t.Fatalf("期望无解: %+v", res)
	}
	checkCycleEvidence(t, in, res.Cycle)
	if len(res.Cycle.Edges) != 1 || res.Cycle.Edges[0].Ref.Kind != KindChildStart {
		t.Fatalf("应为长度 1 的 child_start 自环: %+v", res.Cycle)
	}
}

func TestInfeasibleThroughZeroNode(t *testing.T) {
	// 环经过零点节点：x_b >= 8（界）与 x_b <= 3（经 a 锚点传导）冲突。
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: 8, Hi: 20}},
		Spans: []Span{
			{ID: "s1", Service: "a", Start: 0, End: 3},
			{ID: "s2", Service: "b", Parent: "s1", Start: 0, End: 10},
		},
	}
	res, err := Solve(in)
	if err != nil {
		t.Fatal(err)
	}
	if res.Status != "infeasible" {
		t.Fatalf("期望无解: %+v", res)
	}
	checkCycleEvidence(t, in, res.Cycle)
}

func TestNoSpans(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -2, Hi: 7}},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if res.Offsets["b"] != -2 {
		t.Fatalf("无约束时应取下界 -2，实际 %d", res.Offsets["b"])
	}
	if len(res.Constraints) != 0 || len(res.Spans) != 0 {
		t.Fatalf("无 span 时不应有校正数据: %+v", res)
	}
}

// ---------- 观测 ----------

// 回归：span 端点观测曾被整体忽略（边退化为零点自环），可行输入被判
// 无解且证据只含基准点。
func TestSpanPointObservationFeasible(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -10, Hi: 10}},
		Spans: []Span{
			{ID: "s1", Service: "a", Start: 0, End: 100},
			{ID: "s2", Service: "b", Start: 10, End: 20},
		},
		Observations: []OffsetObservation{
			// s1.start → s2.end 的校正耗时应落在 [5,15]：
			// delta = 20-0 = 20，故 x_b ∈ [-15,-5]。
			{ID: "o1", EarlierSpan: "s1", LaterSpan: "s2",
				EarlierPoint: "start", LaterPoint: "end", Min: 5, Max: 15},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if res.Offsets["b"] != -10 {
		t.Fatalf("字典序最小应在可行域 [-10,-5] 取 -10，实际 %d", res.Offsets["b"])
	}
	if len(res.Observations) != 1 {
		t.Fatalf("缺少观测余量: %+v", res)
	}
	if o := res.Observations[0]; o.Difference != 10 || o.MinSlack != 5 || o.MaxSlack != 5 {
		t.Fatalf("观测余量错误: %+v", o)
	}
}

// 回归：服务间观测的下界边方向曾经写反，解违反观测下界、余量为负。
func TestServiceObservationRespectsMin(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -10, Hi: 10}},
		Observations: []OffsetObservation{
			{ID: "o1", Earlier: "a", Later: "b", Min: 3, Max: 8},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if res.Offsets["b"] != 3 {
		t.Fatalf("x_b 应取观测下界 3，实际 %d", res.Offsets["b"])
	}
	if o := res.Observations[0]; o.Difference != 3 || o.MinSlack != 0 || o.MaxSlack != 5 {
		t.Fatalf("观测余量错误: %+v", o)
	}
}

// 负时间戳 + 混用起止端点：端点本地时刻为负时 delta 同样为负。
func TestSpanObservationNegativeTimestamps(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: 0, Hi: 50}},
		Spans: []Span{
			{ID: "s1", Service: "a", Start: -50, End: -10},
			{ID: "s2", Service: "b", Start: -40, End: -5},
		},
		Observations: []OffsetObservation{
			// s1.end → s2.start：delta = -40-(-10) = -30，
			// 校正差值 ∈ [0,100] => x_b ∈ [30,130]。
			{ID: "o1", EarlierSpan: "s1", LaterSpan: "s2",
				EarlierPoint: "end", LaterPoint: "start", Min: 0, Max: 100},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if res.Offsets["b"] != 30 {
		t.Fatalf("x_b 应在可行域 [30,50] 取 30，实际 %d", res.Offsets["b"])
	}
	if o := res.Observations[0]; o.Difference != 0 || o.MinSlack != 0 || o.MaxSlack != 100 {
		t.Fatalf("观测余量错误: %+v", o)
	}
}

// 多条观测串联时的字典序最小解与逐条余量。
func TestMultipleObservationsLexMin(t *testing.T) {
	in := Input{
		Services: []Service{
			{ID: "a", Lo: 0, Hi: 0},
			{ID: "b", Lo: -10, Hi: 10},
			{ID: "c", Lo: -10, Hi: 10},
		},
		Observations: []OffsetObservation{
			{ID: "o1", Earlier: "a", Later: "b", Min: 2, Max: 5},
			{ID: "o2", Earlier: "b", Later: "c", Min: 1, Max: 4},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	want := map[string]int{"a": 0, "b": 2, "c": 3}
	for id, v := range want {
		if res.Offsets[id] != v {
			t.Fatalf("字典序最小解应为 %+v，实际 %+v", want, res.Offsets)
		}
	}
	if o := res.Observations[0]; o.Difference != 2 || o.MinSlack != 0 || o.MaxSlack != 3 {
		t.Fatalf("观测 o1 余量错误: %+v", o)
	}
	if o := res.Observations[1]; o.Difference != 1 || o.MinSlack != 0 || o.MaxSlack != 3 {
		t.Fatalf("观测 o2 余量错误: %+v", o)
	}
}

// 观测与父子约束、偏移界共同决定可行域。
func TestObservationCombinedWithSpans(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -10, Hi: 10}},
		Spans: []Span{
			{ID: "s1", Service: "a", Start: 0, End: 100},
			{ID: "s2", Service: "b", Parent: "s1", Start: 10, End: 20},
		},
		Observations: []OffsetObservation{
			// 父子包含要求 x_b ∈ [-10,80]；观测再要求 x_b ∈ [4,6]。
			{ID: "o1", Earlier: "a", Later: "b", Min: 4, Max: 6},
			// s2.start → s1.end：差值 = (100+x_a)-(10+x_b) = 90-x_b，
			// 落在 [75,85] => x_b ∈ [5,15]，与上一条交集为 x_b ∈ [5,6]。
			{ID: "o2", EarlierSpan: "s2", LaterSpan: "s1",
				EarlierPoint: "start", LaterPoint: "end", Min: 75, Max: 85},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if res.Offsets["b"] != 5 {
		t.Fatalf("x_b 应在可行域 [5,6] 取 5，实际 %d", res.Offsets["b"])
	}
	if o := res.Observations[0]; o.Difference != 5 || o.MinSlack != 1 || o.MaxSlack != 1 {
		t.Fatalf("观测 o1 余量错误: %+v", o)
	}
	if o := res.Observations[1]; o.Difference != 85 || o.MinSlack != 10 || o.MaxSlack != 0 {
		t.Fatalf("观测 o2 余量错误: %+v", o)
	}
}

// 真正冲突：观测要求 x_b >= 5，b 的上界却是 2。证据须逐边核验，
// 且环中必须包含观测约束边。
func TestObservationConflictInfeasible(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: 0, Hi: 2}},
		Observations: []OffsetObservation{
			{ID: "o1", Earlier: "a", Later: "b", Min: 5, Max: 9},
		},
	}
	res, err := Solve(in)
	if err != nil {
		t.Fatal(err)
	}
	if res.Status != "infeasible" {
		t.Fatalf("期望无解: %+v", res)
	}
	checkCycleEvidence(t, in, res.Cycle)
	hasObsEdge := false
	for _, e := range res.Cycle.Edges {
		if e.Ref.Kind == KindObservationMin || e.Ref.Kind == KindObservationMax {
			hasObsEdge = true
		}
	}
	if !hasObsEdge {
		t.Fatalf("矛盾环应包含观测约束边: %+v", res.Cycle)
	}
}

// 两条观测互相矛盾（区间无交集），同样须给出含观测边的矛盾环。
func TestObservationsMutuallyInfeasible(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -10, Hi: 10}},
		Observations: []OffsetObservation{
			{ID: "o1", Earlier: "a", Later: "b", Min: 5, Max: 8},
			{ID: "o2", Earlier: "a", Later: "b", Min: -4, Max: 2},
		},
	}
	res, err := Solve(in)
	if err != nil {
		t.Fatal(err)
	}
	if res.Status != "infeasible" {
		t.Fatalf("期望无解: %+v", res)
	}
	checkCycleEvidence(t, in, res.Cycle)
}

// 同服务两个 span 端点间的耗时观测：约束不含未知量，直接由本地时刻
// 决定可行与否。
func TestSpanObservationSameService(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -5, Hi: 5}},
		Spans: []Span{
			{ID: "s1", Service: "b", Start: 10, End: 20},
			{ID: "s2", Service: "b", Start: 30, End: 40},
		},
		Observations: []OffsetObservation{
			// s1.end → s2.start 的本地差恒为 10，与 [5,15] 相容。
			{ID: "o1", EarlierSpan: "s1", LaterSpan: "s2",
				EarlierPoint: "end", LaterPoint: "start", Min: 5, Max: 15},
		},
	}
	res, err := Solve(in)
	if err != nil || res.Status != "ok" {
		t.Fatalf("期望可行: %+v err=%v", res, err)
	}
	if o := res.Observations[0]; o.Difference != 10 || o.MinSlack != 5 || o.MaxSlack != 5 {
		t.Fatalf("观测余量错误: %+v", o)
	}
	// 把区间改成 [11,15] 后与恒定的本地差 10 矛盾。
	in.Observations[0].Min = 11
	res, err = Solve(in)
	if err != nil {
		t.Fatal(err)
	}
	if res.Status != "infeasible" {
		t.Fatalf("期望无解: %+v", res)
	}
	checkCycleEvidence(t, in, res.Cycle)
}

// ---------- 校验 ----------

func TestValidate(t *testing.T) {
	ok := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -1, Hi: 1}},
		Spans: []Span{
			{ID: "s1", Service: "a", Start: 0, End: 10},
			{ID: "s2", Service: "b", Parent: "s1", Start: 1, End: 2},
		},
	}
	if errs := Validate(ok); len(errs) != 0 {
		t.Fatalf("合法输入被误判: %v", errs)
	}
	cases := []struct {
		name string
		mut  func(*Input)
	}{
		{"服务过少", func(in *Input) { in.Services = in.Services[:1] }},
		{"服务过多", func(in *Input) {
			for i := 0; i < 7; i++ {
				in.Services = append(in.Services, Service{ID: string(rune('c' + i)), Lo: 0, Hi: 1})
			}
		}},
		{"无锚定", func(in *Input) { in.Services[0].Hi = 1 }},
		{"双锚定", func(in *Input) { in.Services[1].Lo, in.Services[1].Hi = 0, 0 }},
		{"界颠倒", func(in *Input) { in.Services[1].Lo, in.Services[1].Hi = 5, -5 }},
		{"服务ID重复", func(in *Input) { in.Services[1].ID = "a" }},
		{"服务ID为空", func(in *Input) { in.Services[1].ID = "" }},
		{"span过多", func(in *Input) {
			for i := 0; i < 101; i++ {
				in.Spans = append(in.Spans, Span{ID: "x" + string(rune(i)), Service: "a", Start: 0, End: 1})
			}
		}},
		{"spanID重复", func(in *Input) { in.Spans[1].ID = "s1" }},
		{"spanID为空", func(in *Input) { in.Spans[1].ID = "" }},
		{"未知服务", func(in *Input) { in.Spans[1].Service = "zz" }},
		{"起终颠倒", func(in *Input) { in.Spans[0].Start, in.Spans[0].End = 9, 1 }},
		{"父span不存在", func(in *Input) { in.Spans[1].Parent = "ghost" }},
		{"父链成环", func(in *Input) {
			in.Spans[0].Parent = "s2"
			in.Spans[1].Parent = "s1"
		}},
		{"量级超限", func(in *Input) { in.Spans[0].End = maxAbs + 1 }},
		{"观测区间颠倒", func(in *Input) {
			in.Observations = []OffsetObservation{{ID: "o1", Earlier: "a", Later: "b", Min: 6, Max: 5}}
		}},
		{"观测服务对相同", func(in *Input) {
			in.Observations = []OffsetObservation{{ID: "o1", Earlier: "a", Later: "a", Min: 0, Max: 1}}
		}},
		{"观测引用未知服务", func(in *Input) {
			in.Observations = []OffsetObservation{{ID: "o1", Earlier: "a", Later: "zz", Min: 0, Max: 1}}
		}},
		{"观测ID重复", func(in *Input) {
			in.Observations = []OffsetObservation{
				{ID: "o1", Earlier: "a", Later: "b", Min: 0, Max: 1},
				{ID: "o1", Earlier: "a", Later: "b", Min: 0, Max: 1},
			}
		}},
		{"观测span不存在", func(in *Input) {
			in.Observations = []OffsetObservation{{ID: "o1", EarlierSpan: "ghost", LaterSpan: "s1",
				EarlierPoint: "start", LaterPoint: "end", Min: 0, Max: 1}}
		}},
		{"观测只给了一个span", func(in *Input) {
			in.Observations = []OffsetObservation{{ID: "o1", EarlierSpan: "s1",
				EarlierPoint: "start", LaterPoint: "end", Min: 0, Max: 1}}
		}},
		{"观测端点无效", func(in *Input) {
			in.Observations = []OffsetObservation{{ID: "o1", EarlierSpan: "s1", LaterSpan: "s2",
				EarlierPoint: "middle", LaterPoint: "end", Min: 0, Max: 1}}
		}},
		{"观测服务与span不符", func(in *Input) {
			in.Observations = []OffsetObservation{{ID: "o1", Earlier: "b", EarlierSpan: "s1", LaterSpan: "s2",
				EarlierPoint: "start", LaterPoint: "end", Min: 0, Max: 1}}
		}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			in := ok
			in.Services = append([]Service(nil), ok.Services...)
			in.Spans = append([]Span(nil), ok.Spans...)
			tc.mut(&in)
			if errs := Validate(in); len(errs) == 0 {
				t.Fatalf("应检出非法输入")
			}
		})
	}
}

// 两种形态的合法观测（含服务字段与 span 服务一致的冗余填写）都应通过校验。
func TestValidateObservationsOK(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "a", Lo: 0, Hi: 0}, {ID: "b", Lo: -1, Hi: 1}},
		Spans: []Span{
			{ID: "s1", Service: "a", Start: 0, End: 10},
			{ID: "s2", Service: "b", Parent: "s1", Start: 1, End: 2},
		},
		Observations: []OffsetObservation{
			{ID: "o1", Earlier: "a", Later: "b", Min: -1, Max: 1},
			{ID: "o2", EarlierSpan: "s1", LaterSpan: "s2",
				EarlierPoint: "start", LaterPoint: "end", Min: 0, Max: 10},
			{ID: "o3", Earlier: "a", Later: "b", EarlierSpan: "s1", LaterSpan: "s2",
				EarlierPoint: "end", LaterPoint: "start", Min: -10, Max: 0},
		},
	}
	if errs := Validate(in); len(errs) != 0 {
		t.Fatalf("合法观测被误判: %v", errs)
	}
}

// 排序稳定性：order 必须是服务 ID 的升序。
func TestOrderSorted(t *testing.T) {
	in := Input{
		Services: []Service{{ID: "zz", Lo: -1, Hi: 1}, {ID: "aa", Lo: 0, Hi: 0}},
	}
	_, _, order, _ := buildGraph(in)
	if !sort.StringsAreSorted(order) || order[0] != "aa" {
		t.Fatalf("order 应为 ID 升序: %v", order)
	}
}
