import LeanIsing.Engine

/-!
# 層つき模型の実行系

ボンドの層ごとに Boltzmann 因子をもつ模型（`Model`）の Metropolis 法。
反転するサイトの近傍だけを見て、局所比 `r = Π_l x_l ^ agree_l / x_l ^ disagree_l` から受理確率
`A = min(1, r)` を厳密な有理数で計算する。

層が 2 つ以上あると、`r` の分母には因子の分子も現れうる（例：`x^2 / y`）。そこで一様乱数
`u = k / D` の分母を、受理確率そのものの分母 `D = A.den` に合わせる。`k` が `{0, …, D - 1}` 上で
一様なら `P(u < A) = A.num / A.den = A` が丸めなしに成り立つ。

`inducedKernel` が仕様の `Model.kernel` に等しいことは `Proofs.Layered` で証明する。
-/

namespace LeanIsing

/-- ボンドの集合 `bs` におけるサイト `i` の隣。 -/
def nbrsOf {n : Nat} (bs : List (Fin n × Fin n)) (i : Fin n) : List (Fin n) :=
  Graph.nbrs ⟨n, bs⟩ i

namespace Layered

open Engine Rng

/-- `x^a / x^d` を、約分の要らない `x^(a-d)` または `(x⁻¹)^(d-a)` として計算する
（`x ≠ 0` なら等しい：`Proofs.Layered.ratioPow_eq`）。 -/
def ratioPow (x : Rat) (a d : Nat) : Rat :=
  if d ≤ a then x ^ (a - d) else x⁻¹ ^ (d - a)

/-- 局所比 `Π_l x_l ^ agree_l / x_l ^ disagree_l`（サイト `i` を反転したときの重みの比）。 -/
def localRatio {n : Nat} (σ : Config n) (i : Fin n) : List (List (Fin n) × Rat) → Rat
  | [] => 1
  | l :: rest => ratioPow l.2 (agree l.1 σ i) (disagree l.1 σ i) * localRatio σ i rest

/-- 近傍だけから計算した受理確率 `min(1, r)`。 -/
def acceptLocal {n : Nat} (nbl : List (List (Fin n) × Rat)) (σ : Config n) (i : Fin n) : Rat :=
  min 1 (localRatio σ i nbl)

/-- 乱数 `(i, u)` を与えたときの 1 ステップ（決定的）。 -/
def step {n : Nat} (nbl : List (List (Fin n) × Rat)) (σ : Config n) (i : Fin n) (u : Rat) : Config n :=
  if u < acceptLocal nbl σ i then flip σ i else σ

/-- 受理確率 `A` を計算済みのときの 1 ステップ：`u = k / A.den` を作り、`u < A` なら反転する。
受理したかどうかも返す。 -/
@[inline] def stepWithA {n : Nat} (A : Rat) (σ : Config n) (i : Fin n) (k : Nat) : Config n × Bool :=
  if mkRat k A.den < A then (flip σ i, true) else (σ, false)

/-- サイト `i` の、層ごとの隣と因子。 -/
def nbrLayers (M : Model) (i : Fin M.n) : List (List (Fin M.n) × Rat) :=
  M.layers.map fun l => (nbrsOf l.1 i, l.2)

/-- 実装が動かしているマルコフ連鎖の遷移確率：サイト `i` を一様に選び、受理確率
`A = acceptLocal σ i` の分母 `D = A.den` について `u = k / D`（`k ∈ {0, …, D - 1}` が一様）とする。 -/
def inducedKernel (M : Model) (σ τ : Config M.n) : Rat :=
  ((List.finRange M.n).map fun i =>
      (((List.range (acceptLocal (nbrLayers M i) σ i).den).countP fun (k : Nat) =>
          decide (step (nbrLayers M i) σ i
            ((k : Rat) / (acceptLocal (nbrLayers M i) σ i).den) = τ) : Nat) : Rat) /
        (acceptLocal (nbrLayers M i) σ i).den).sum / M.n

/-- 層つき模型のシミュレーションの設定と前計算。 -/
structure Sim where
  M : Model
  /-- `tables[i] = nbrLayers M i`。 -/
  tables : Vector (List (List (Fin M.n) × Rat)) M.n
  siteU : Rng.Uniform

def Sim.make (M : Model) : Sim :=
  { M, tables := Vector.ofFn (nbrLayers M), siteU := .make M.n }

namespace Sim

variable (s : Sim)

/-- 乱数 `i` と `k` を与えたときの 1 ステップ。`u = k / D`（`D` は受理確率の分母）を厳密有理数として作る。
第 1 成分が `step` に等しいことは `Proofs.Layered.Layered.Sim.stepPure_fst`。 -/
def stepPure (σ : Config s.M.n) (i : Fin s.M.n) (k : Nat) : Config s.M.n × Bool :=
  stepWithA (acceptLocal s.tables[i] σ i) σ i k

/-- 1 ステップ：サイト `i` を一様に引き、受理確率 `A` の分母 `D` について `k ∈ [0, D)` を一様に引く。
返り値は `s.stepPure σ i k` と定義上等しい（`A` を 1 回だけ計算する）。 -/
def stepM (h : 0 < s.M.n) (σ : Config s.M.n) : RandM (Config s.M.n × Bool) := do
  let i0 ← s.siteU.sample
  let i : Fin s.M.n := ⟨i0 % s.M.n, Nat.mod_lt _ h⟩
  let A := acceptLocal s.tables[i] σ i
  let k ← uniformNat A.den
  return stepWithA A σ i k

/-- 1 スイープ（`n` ステップ）。受理数も返す。 -/
def sweep (h : 0 < s.M.n) (σ : Config s.M.n) : RandM (Config s.M.n × Nat) := do
  let mut σ := σ
  let mut acc := 0
  for _ in [0:s.M.n] do
    let (σ', a) ← s.stepM h σ
    σ := σ'
    if a then acc := acc + 1
  return (σ, acc)

end Sim

end Layered

end LeanIsing
