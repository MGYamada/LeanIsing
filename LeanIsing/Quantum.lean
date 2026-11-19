import LeanIsing.Spec

/-!
# 横磁場 Ising 模型と経路積分（世界線）表示（仕様）

空間グラフ `G`（`N` サイト）上の横磁場 Ising 模型

  `H = -J Σ_{⟨ij⟩ ∈ G} σᶻ_i σᶻ_j - Γ Σ_i σˣ_i`

を、Trotter 数 `M`、`ε = β/M` で分解する（Suzuki–Trotter）：

  `Z_M = Tr (e^{εJ Σ σᶻσᶻ} e^{εΓ Σ σˣ})^M`。

`e^{aσˣ} = cosh a · (1 + tanh a · σˣ)` なので、`σᶻ` 基底での行列要素は

  `⟨s| e^{εJ Σσᶻσᶻ} e^{εΓ Σσˣ} |s'⟩ = C · x^{unsat_G(s)} · y^{#{i : s_i ≠ s'_i}}`、
  `x = e^{-2εJ}`、`y = tanh(εΓ)`、`C = e^{εJ|bonds|} (cosh εΓ)^N`（定数）

となる。`x`、`y` を有理数にとれば、転送行列（定数倍を除く）`transfer` は有理数の行列であり、
世界線 `(s_0, …, s_{M-1})`（`s_M = s_0`）の重み `Π_τ transfer(s_τ, s_{τ+1})`（`pathWeight`）も
厳密な有理数になる。この重みは、空間 × 虚時間の格子上の 2 層の Ising 模型 `trotter G M x y`
（空間方向の因子 `x`、虚時間方向の因子 `y`）の重みに等しい（`Proofs.Quantum.trotter_weight`）。
したがって、その模型の Metropolis 法が経路積分量子モンテカルロ法になる。

`M = 1` では虚時間方向のボンドが自己ループになり、横磁場の寄与が消えて古典模型に戻る。
-/

namespace LeanIsing.Quantum

/-- 世界線上のサイト `(i, τ)` の番号 `N·τ + i`（スライス `τ` ごとに `N` 個並べる）。 -/
def idx {N M : Nat} (τ : Fin M) (i : Fin N) : Fin (N * M) :=
  ⟨N * τ + i, by
    have h : N * τ + N ≤ N * M := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left N τ.isLt
    have := i.isLt
    omega⟩

/-- 虚時間の次の時刻（周期境界）。 -/
def next {M : Nat} (τ : Fin M) : Fin M :=
  ⟨(τ.val + 1) % M, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) τ.isLt)⟩

/-- 世界線の、時刻 `τ` のスライス。 -/
def slice {N M : Nat} (s : Config (N * M)) (τ : Fin M) : Config N :=
  Vector.ofFn fun i => s[idx τ i]

/-- 2 つの配位の、向きの異なるサイトの数。 -/
def hamming {N : Nat} (s s' : Config N) : Nat :=
  (List.finRange N).countP fun i => s[i] != s'[i]

/-- Trotter 転送行列（定数倍を除く）：`transfer(s, s') = x^{unsat_G(s)} · y^{hamming(s, s')}`。 -/
def transfer (G : Graph) (x y : Rat) (s s' : Config G.n) : Rat :=
  x ^ G.unsat s * y ^ hamming s s'

/-- 世界線の重み `Π_τ transfer(s_τ, s_{τ+1})`（`s_M = s_0`）。 -/
def pathWeight (G : Graph) (M : Nat) (x y : Rat) (s : Config (G.n * M)) : Rat :=
  ((List.finRange M).map fun τ => transfer G x y (slice s τ) (slice s (next τ))).prod

/-- 空間方向のボンド：各スライスに `G` のボンドを張る。 -/
def spaceBonds (G : Graph) (M : Nat) : List (Fin (G.n * M) × Fin (G.n * M)) :=
  (List.finRange M).flatMap fun τ => G.bonds.map fun b => (idx τ b.1, idx τ b.2)

/-- 虚時間方向のボンド：`(i, τ)` と `(i, τ + 1)` を結ぶ。 -/
def timeBonds (N M : Nat) : List (Fin (N * M) × Fin (N * M)) :=
  (List.finRange M).flatMap fun τ => (List.finRange N).map fun i => (idx τ i, idx (next τ) i)

/-- 経路積分表示の 2 層の Ising 模型（空間方向の因子 `x`、虚時間方向の因子 `y`）。 -/
def trotter (G : Graph) (M : Nat) (x y : Rat) : Model where
  n := G.n * M
  layers := [(spaceBonds G M, x), (timeBonds G.n M, y)]

/-- 経路積分の重みによる世界線の分布（量子モンテカルロ法の目標分布）。 -/
def pathDistribution (G : Graph) (M : Nat) (x y : Rat) : Config (G.n * M) → Rat :=
  normalize (pathWeight G M x y)

end LeanIsing.Quantum
