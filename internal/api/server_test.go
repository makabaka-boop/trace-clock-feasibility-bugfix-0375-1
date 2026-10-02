package api

import (
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"clocksync/internal/solver"
)

func newServer() http.Handler {
	return New(nil)
}

func postSolve(t *testing.T, body string) *httptest.ResponseRecorder {
	t.Helper()
	req := httptest.NewRequest("POST", "/api/solve", strings.NewReader(body))
	rec := httptest.NewRecorder()
	newServer().ServeHTTP(rec, req)
	return rec
}

func TestSolveOK(t *testing.T) {
	rec := postSolve(t, `{
		"services": [{"id":"a","lo":0,"hi":0},{"id":"b","lo":-10,"hi":10}],
		"spans": [
			{"id":"s1","service":"a","parent":"","start":0,"end":100},
			{"id":"s2","service":"b","parent":"s1","start":-3,"end":0}
		]
	}`)
	if rec.Code != http.StatusOK {
		t.Fatalf("状态码 %d: %s", rec.Code, rec.Body)
	}
	var res solver.Result
	if err := json.Unmarshal(rec.Body.Bytes(), &res); err != nil {
		t.Fatal(err)
	}
	if res.Status != "ok" {
		t.Fatalf("期望 ok: %s", rec.Body)
	}
	if res.Offsets["b"] != 3 || res.Offsets["a"] != 0 {
		t.Fatalf("偏移错误: %+v", res.Offsets)
	}
	if len(res.Spans) != 2 || len(res.Constraints) != 1 {
		t.Fatalf("校正数据缺失: %+v", res)
	}
	c := res.Constraints[0]
	if c.StartSlack != 0 || c.EndSlack != 97 {
		t.Fatalf("余量错误: %+v", c)
	}
	// 校正时刻必须与偏移一致。
	for _, sp := range res.Spans {
		if sp.CorrectedStart != sp.Start+res.Offsets[sp.Service] ||
			sp.CorrectedEnd != sp.End+res.Offsets[sp.Service] {
			t.Fatalf("校正时刻与偏移不一致: %+v", sp)
		}
	}
}

// 无解响应不得携带任何可用于绘制时间线的字段。
func TestSolveInfeasibleHasNoTimelineData(t *testing.T) {
	rec := postSolve(t, `{
		"services": [{"id":"a","lo":0,"hi":0},{"id":"b","lo":8,"hi":20}],
		"spans": [
			{"id":"s1","service":"a","parent":"","start":0,"end":3},
			{"id":"s2","service":"b","parent":"s1","start":0,"end":10}
		]
	}`)
	if rec.Code != http.StatusOK {
		t.Fatalf("状态码 %d: %s", rec.Code, rec.Body)
	}
	var raw map[string]any
	if err := json.Unmarshal(rec.Body.Bytes(), &raw); err != nil {
		t.Fatal(err)
	}
	if raw["status"] != "infeasible" {
		t.Fatalf("期望 infeasible: %s", rec.Body)
	}
	for _, k := range []string{"offsets", "spans", "constraints", "order", "observations"} {
		if _, present := raw[k]; present {
			t.Fatalf("无解响应不得包含字段 %q: %s", k, rec.Body)
		}
	}
	cyc, ok := raw["cycle"].(map[string]any)
	if !ok {
		t.Fatalf("缺少矛盾环: %s", rec.Body)
	}
	edges, ok := cyc["edges"].([]any)
	if !ok || len(edges) == 0 {
		t.Fatalf("矛盾环为空: %s", rec.Body)
	}
	if w, _ := cyc["totalWeight"].(float64); w >= 0 {
		t.Fatalf("矛盾环总权重应为负: %v", w)
	}
}

// 两种形态的观测一起求解：响应须携带逐条观测余量，且与偏移自洽。
func TestSolveWithObservations(t *testing.T) {
	rec := postSolve(t, `{
		"services": [{"id":"a","lo":0,"hi":0},{"id":"b","lo":-10,"hi":10}],
		"spans": [
			{"id":"s1","service":"a","parent":"","start":0,"end":100},
			{"id":"s2","service":"b","parent":"","start":10,"end":20}
		],
		"observations": [
			{"id":"o1","earlierSpan":"s1","laterSpan":"s2","earlierPoint":"start","laterPoint":"end","min":5,"max":15},
			{"id":"o2","earlier":"a","later":"b","min":-10,"max":-5}
		]
	}`)
	if rec.Code != http.StatusOK {
		t.Fatalf("状态码 %d: %s", rec.Code, rec.Body)
	}
	var res solver.Result
	if err := json.Unmarshal(rec.Body.Bytes(), &res); err != nil {
		t.Fatal(err)
	}
	if res.Status != "ok" {
		t.Fatalf("期望 ok: %s", rec.Body)
	}
	// o1 要求 x_b ∈ [-15,-5]，o2 要求 x_b ∈ [-10,-5]，字典序最小取 -10。
	if res.Offsets["b"] != -10 {
		t.Fatalf("偏移错误: %+v", res.Offsets)
	}
	if len(res.Observations) != 2 {
		t.Fatalf("缺少观测余量: %s", rec.Body)
	}
	wantDiff := map[string]int{"o1": 10, "o2": -10}
	for _, o := range res.Observations {
		if o.Difference != wantDiff[o.ID] {
			t.Fatalf("观测 %s 差值错误: %+v", o.ID, o)
		}
		if o.MinSlack < 0 || o.MaxSlack < 0 {
			t.Fatalf("观测 %s 余量为负: %+v", o.ID, o)
		}
	}
}

// 观测与偏移界冲突时判无解，证据须含观测约束边且不携带时间线字段。
func TestSolveObservationConflict(t *testing.T) {
	rec := postSolve(t, `{
		"services": [{"id":"a","lo":0,"hi":0},{"id":"b","lo":0,"hi":2}],
		"spans": [],
		"observations": [{"id":"o1","earlier":"a","later":"b","min":5,"max":9}]
	}`)
	if rec.Code != http.StatusOK {
		t.Fatalf("状态码 %d: %s", rec.Code, rec.Body)
	}
	var raw map[string]any
	if err := json.Unmarshal(rec.Body.Bytes(), &raw); err != nil {
		t.Fatal(err)
	}
	if raw["status"] != "infeasible" {
		t.Fatalf("期望 infeasible: %s", rec.Body)
	}
	for _, k := range []string{"offsets", "spans", "constraints", "order", "observations"} {
		if _, present := raw[k]; present {
			t.Fatalf("无解响应不得包含字段 %q: %s", k, rec.Body)
		}
	}
	cyc, ok := raw["cycle"].(map[string]any)
	if !ok {
		t.Fatalf("缺少矛盾环: %s", rec.Body)
	}
	edges, ok := cyc["edges"].([]any)
	if !ok || len(edges) == 0 {
		t.Fatalf("矛盾环为空: %s", rec.Body)
	}
	hasObsEdge := false
	for _, e := range edges {
		edge, _ := e.(map[string]any)
		ref, _ := edge["ref"].(map[string]any)
		if k, _ := ref["kind"].(string); k == "observation_min" || k == "observation_max" {
			hasObsEdge = true
		}
	}
	if !hasObsEdge {
		t.Fatalf("矛盾环应包含观测约束边: %s", rec.Body)
	}
}

func TestSolveInvalidInput(t *testing.T) {
	rec := postSolve(t, `{"services":[{"id":"a","lo":0,"hi":0}],"spans":[]}`)
	if rec.Code != http.StatusBadRequest {
		t.Fatalf("状态码 %d", rec.Code)
	}
	var body struct {
		Errors []string `json:"errors"`
	}
	if err := json.Unmarshal(rec.Body.Bytes(), &body); err != nil || len(body.Errors) == 0 {
		t.Fatalf("应返回错误列表: %s", rec.Body)
	}
}

func TestSolveRejectsUnknownFields(t *testing.T) {
	rec := postSolve(t, `{"services":[],"spans":[],"bogus":1}`)
	if rec.Code != http.StatusBadRequest {
		t.Fatalf("未知字段应被拒绝，状态码 %d", rec.Code)
	}
}

func TestSolveRejectsMalformedJSON(t *testing.T) {
	rec := postSolve(t, `{not json`)
	if rec.Code != http.StatusBadRequest {
		t.Fatalf("状态码 %d", rec.Code)
	}
}

// 两个示例端点自身必须与求解器结论一致。
func TestExamplesAreConsistent(t *testing.T) {
	for _, tc := range []struct {
		kind, want string
	}{{"feasible", "ok"}, {"infeasible", "infeasible"}} {
		req := httptest.NewRequest("GET", "/api/example?kind="+tc.kind, nil)
		rec := httptest.NewRecorder()
		newServer().ServeHTTP(rec, req)
		if rec.Code != http.StatusOK {
			t.Fatalf("%s: 状态码 %d", tc.kind, rec.Code)
		}
		var in solver.Input
		if err := json.Unmarshal(rec.Body.Bytes(), &in); err != nil {
			t.Fatalf("%s: %v", tc.kind, err)
		}
		if errs := solver.Validate(in); len(errs) != 0 {
			t.Fatalf("%s 示例未通过校验: %v", tc.kind, errs)
		}
		res, err := solver.Solve(in)
		if err != nil || res.Status != tc.want {
			t.Fatalf("%s 示例求解结果应为 %s: %+v err=%v", tc.kind, tc.want, res, err)
		}
	}
}
