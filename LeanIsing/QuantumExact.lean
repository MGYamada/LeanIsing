import LeanIsing.Quantum

/-!
# 小さな横磁場 Ising 模型の厳密値（転送行列）

`N` が小さければ、Trotter 転送行列 `T(s, s') = x^{unsat s} y^{hamming(s, s')}`（`2^N × 2^N` の有理数行列）を
そのまま掛け合わせて、量子モンテカルロ法と**同じ Trotter 数 `M` での**期待値を厳密な有理数で計算できる。

* `Z_M = Tr T^M`
* `⟨σᶻσᶻ⟩`（ボンドあたり）`= Tr(C T^M) / Z_M`、`C = diag(1 - 2 unsat(s) / |bonds|)`
* `⟨σˣ⟩`（サイトあたり）`= Tr(T^{M-1} (T ∘ R)) / Z_M`、
  `R(s, s') = ((N - h) y + h / y) / N`（`h = hamming(s, s')`）。
  `σˣ e^{aσˣ}` と `e^{aσˣ}` の行列要素の比が `tanh a = y`（同じ向き）または `1 / y`（逆向き）であることによる。

モンテカルロ法の推定量（`LeanIsing.App`）はこれらと同じ量を世界線の平均として求める。
-/

namespace LeanIsing.QuantumExact

open Quantum

abbrev Mat := Array (Array Rat)

def matMul (A B : Mat) : Mat :=
  let k := B.size
  A.map fun row => (List.range (B[0]?.getD #[]).size).toArray.map fun j =>
    (List.range k).foldl (fun s l => s + row[l]! * B[l]![j]!) 0

def matPow (A : Mat) : Nat → Mat
  | 0 => A.mapIdx fun i row => row.mapIdx fun j _ => if i == j then 1 else 0
  | m + 1 => matMul A (matPow A m)

def trace (A : Mat) : Rat := (List.range A.size).foldl (fun s i => s + A[i]![i]!) 0

structure Values where
  /-- ボンドあたりの `⟨σᶻσᶻ⟩`。 -/
  zz : Rat
  /-- サイトあたりの `⟨σˣ⟩`。 -/
  sx : Rat

/-- 同じ `M` での厳密な期待値（`M ≥ 1`、ボンドが 1 本以上）。 -/
def values (G : Graph) (M : Nat) (x y : Rat) : Values := Id.run do
  let cs := (allConfigs G.n).toArray
  let N : Rat := G.n
  let B : Rat := G.bonds.length
  let T : Mat := cs.map fun s => cs.map fun s' => transfer G x y s s'
  let TR : Mat := cs.map fun s => cs.map fun s' =>
    let h : Rat := hamming s s'
    transfer G x y s s' * (((N - h) * y + h / y) / N)
  let TM1 := matPow T (M - 1)
  let TM := matMul TM1 T
  let Z := trace TM
  let mut czz : Rat := 0
  for i in [0:cs.size] do
    czz := czz + (1 - 2 * (G.unsat cs[i]! : Rat) / B) * TM[i]![i]!
  let sx := trace (matMul TM1 TR)
  return { zz := czz / Z, sx := sx / Z }

end LeanIsing.QuantumExact
