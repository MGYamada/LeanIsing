import LeanIsing.Spec
import LeanIsing.Rng

/-!
# Metropolis 法の実行系

シミュレーションが実際に使う関数。仕様（`LeanIsing.Spec`）の `accept` は大域的な重み
`x ^ unsat σ` の比で定義されているが、ここでは反転するサイトの近傍だけを見て受理確率を計算する。
両者が一致すること、そして乱数 `(i, u)` が一様なときに `step` が引き起こす遷移確率
`inducedKernel` が仕様の `kernel` に**厳密に等しい**ことは `Proofs.Exactness` で証明する。
-/

namespace LeanIsing

namespace Graph

variable (G : Graph)

/-- サイト `i` の隣（`i` を端点とする自己ループでないボンドの相手側。多重ボンドは重複して数える）。 -/
def nbrs (i : Fin G.n) : List (Fin G.n) :=
  G.bonds.filterMap fun b =>
    if b.1 = i ∧ b.2 ≠ i then some b.2 else if b.2 = i ∧ b.1 ≠ i then some b.1 else none

end Graph

namespace Engine

open Rng

/-- 隣のうち、サイト `i` と同じ向きのスピンの数。 -/
def agree {n : Nat} (nb : List (Fin n)) (σ : Config n) (i : Fin n) : Nat :=
  nb.countP fun j => σ[j] == σ[i]

/-- 隣のうち、サイト `i` と逆向きのスピンの数。 -/
def disagree {n : Nat} (nb : List (Fin n)) (σ : Config n) (i : Fin n) : Nat :=
  nb.countP fun j => σ[j] != σ[i]

/-- 近傍だけから計算する受理確率。サイト `i` を反転すると不満足ボンドは
`agree - disagree` 本増える（`Proofs.Exactness.unsat_flip`）ので、`0 < x ≤ 1` のとき
`min(1, x ^ (agree - disagree))` が仕様の `accept` に等しい。 -/
def acceptLocal {n : Nat} (x : Rat) (nb : List (Fin n)) (σ : Config n) (i : Fin n) : Rat :=
  let a := agree nb σ i
  let d := disagree nb σ i
  if a ≤ d then 1 else x ^ (a - d)

/-- 乱数 `(i, u)` を与えたときの 1 ステップ（決定的）。`u < 受理確率` なら反転する。 -/
def step {n : Nat} (x : Rat) (nb : List (Fin n)) (σ : Config n) (i : Fin n) (u : Rat) : Config n :=
  if u < acceptLocal x nb σ i then flip σ i else σ

/-- `step` と同じ計算で、受理したかどうかも返す（シミュレーションの統計用）。
第 1 成分は `step` に等しい（`Proofs.Theorems.Sim.stepPure_fst'`）。 -/
def stepWithFlag {n : Nat} (x : Rat) (nb : List (Fin n)) (σ : Config n) (i : Fin n) (u : Rat) :
    Config n × Bool :=
  if u < acceptLocal x nb σ i then (flip σ i, true) else (σ, false)

/-- 実装が動かしているマルコフ連鎖の遷移確率：サイト `i ∈ Fin n` と
`u = k / D`（`k ∈ {0, …, D - 1}`）が一様に選ばれるとき、`step` が `σ` を `τ` に移す確率。
（`n · D` 通りの乱数のうち、`τ` に移るものの割合。） -/
def inducedKernel (G : Graph) (x : Rat) (D : Nat) (σ τ : Config G.n) : Rat :=
  (((List.finRange G.n).map fun i =>
      (List.range D).countP fun (k : Nat) => decide (step x (G.nbrs i) σ i ((k : Rat) / D) = τ)).sum : Nat) /
    ((G.n : Rat) * D)

/-- 隣接表の各リストの長さの最大値（最大次数）。 -/
def maxLen {n : Nat} (tbl : Vector (List (Fin n)) n) : Nat :=
  (List.finRange n).foldl (fun m i => max m tbl[i].length) 0

/-- シミュレーションの設定と前計算。 -/
structure Sim where
  G : Graph
  /-- 温度パラメータ `x = exp(-2βJ)`（`0 < x ≤ 1`）。 -/
  x : Rat
  /-- 隣接表。`nbrTable[i] = G.nbrs i`。 -/
  nbrTable : Vector (List (Fin G.n)) G.n
  /-- 一様乱数 `u = k / D` の分母。 -/
  D : Nat
  /-- サイト `i ∈ [0, n)` と `k ∈ [0, D)` を引くための前計算。 -/
  siteU : Rng.Uniform
  kU : Rng.Uniform

/-- 設定を作る。乱数の分母は `D = (x の分母) ^ (最大次数)` にとる。受理確率 `x ^ Δ`（`Δ ≤ 最大次数`）は
すべて `D` で割り切れる分母をもつので、`u = k / D` との比較で受理確率が**丸めなしに**再現される。 -/
def Sim.make (G : Graph) (x : Rat) : Sim :=
  let tbl := Vector.ofFn G.nbrs
  let D := x.den ^ maxLen tbl
  { G, x, nbrTable := tbl, D, siteU := .make G.n, kU := .make D }

/-- 統計量の累積。 -/
structure Stats where
  /-- 測定回数（スイープ数）。 -/
  samples : Nat := 0
  /-- `Σ E`、`Σ E²`。 -/
  sumE : Int := 0
  sumE2 : Nat := 0
  /-- `Σ |M|`、`Σ M²`、`Σ M⁴`。 -/
  sumAbsM : Nat := 0
  sumM2 : Nat := 0
  sumM4 : Nat := 0
  /-- 受理された反転の数と、提案の総数。 -/
  accepted : Nat := 0
  proposed : Nat := 0
  deriving Repr, Inhabited

namespace Sim

variable (s : Sim)

/-- 乱数 `i`、`k` を与えたときの 1 ステップ。`u = k / D` を厳密有理数として作り、`step` を適用する。
`Sim.make G x` に対しては第 1 成分が `step x (G.nbrs i) σ i ((k : Rat) / D)` に等しい
（`Proofs.Theorems.Sim.stepPure_fst`）。 -/
def stepPure (σ : Config s.G.n) (i : Fin s.G.n) (k : Nat) : Config s.G.n × Bool :=
  stepWithFlag s.x s.nbrTable[i] σ i (mkRat k s.D)

/-- 1 ステップ：一様乱数 `i ∈ [0, n)`、`k ∈ [0, D)` を引いて `stepPure` を適用する。 -/
def stepM (h : 0 < s.G.n) (σ : Config s.G.n) : RandM (Config s.G.n × Bool) := do
  let i ← s.siteU.sample
  let k ← s.kU.sample
  return s.stepPure σ ⟨i % s.G.n, Nat.mod_lt _ h⟩ k

/-- 1 スイープ（`n` ステップ）。受理数も返す。 -/
def sweep (h : 0 < s.G.n) (σ : Config s.G.n) : RandM (Config s.G.n × Nat) := do
  let mut σ := σ
  let mut acc := 0
  for _ in [0:s.G.n] do
    let (σ', a) ← s.stepM h σ
    σ := σ'
    if a then acc := acc + 1
  return (σ, acc)

/-- 配位の観測値を統計に加える。 -/
def record (st : Stats) (σ : Config s.G.n) (acc : Nat) : Stats :=
  let e := s.G.energy σ
  let m := (s.G.magnetization σ).natAbs
  { samples := st.samples + 1
    sumE := st.sumE + e
    sumE2 := st.sumE2 + e.natAbs ^ 2
    sumAbsM := st.sumAbsM + m
    sumM2 := st.sumM2 + m ^ 2
    sumM4 := st.sumM4 + m ^ 4
    accepted := st.accepted + acc
    proposed := st.proposed + s.G.n }

/-- `therm` スイープ捨ててから `meas` スイープ測定する。 -/
def run (h : 0 < s.G.n) (σ : Config s.G.n) (therm meas : Nat) :
    RandM (Config s.G.n × Stats) := do
  let mut σ := σ
  for _ in [0:therm] do
    σ := (← s.sweep h σ).1
  let mut st : Stats := {}
  for _ in [0:meas] do
    let (σ', acc) ← s.sweep h σ
    σ := σ'
    st := s.record st σ acc
  return (σ, st)

end Sim

/-- 一様ランダムな配位（高温からの開始用）。 -/
def randomConfig (n : Nat) : RandM (Config n) := do
  let mut v : Array Bool := Array.mkEmpty n
  for _ in [0:n] do
    v := v.push ((← Rng.uniformNat 2) == 1)
  if h : v.size = n then return ⟨v, h⟩ else return allUp n

end Engine

end LeanIsing
