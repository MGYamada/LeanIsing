import LeanIsing

/-!
# 実行系の単体テスト

`lake build` のたびに評価される（`#guard` が `false` ならビルドが失敗する）。
証明（`Proofs/`）が一般に保証していることを、小さな系で実際に計算して確かめる。
-/

namespace LeanIsing.Tests

open Engine Rng Numeric

/-- 全配位の対。 -/
def allPairs (n : Nat) : List (Config n × Config n) :=
  (allConfigs n).flatMap fun σ => (allConfigs n).map fun τ => (σ, τ)

/-- 遷移行列を配列として作る（`allConfigs` の順）。 -/
def matrix {n : Nat} (P : Config n → Config n → Rat) : Array (Array Rat) :=
  ((allConfigs n).map fun σ => ((allConfigs n).map fun τ => P σ τ).toArray).toArray

def matMul (A B : Array (Array Rat)) : Array (Array Rat) :=
  A.map fun row => (List.range row.size).toArray.map fun j =>
    (List.range row.size).foldl (fun s k => s + row[k]! * B[k]![j]!) 0

def matPow (A : Array (Array Rat)) : Nat → Array (Array Rat)
  | 0 => A.mapIdx fun i row => row.mapIdx fun j _ => if i == j then 1 else 0
  | m + 1 => matMul A (matPow A m)

def G3 := Lattice.ring 3
def G4 := Lattice.ring 4
def S2 := Lattice.square 2
def S3 := Lattice.square 3

/-! ## 格子 -/

#guard (allConfigs 3).length == 8
#guard S3.n == 9 && S3.bonds.length == 18
-- 3×3 正方格子では、どのサイトにも上下左右の 4 個の隣がある
#guard (List.finRange S3.n).all fun i => (S3.nbrs i).length == 4
-- 2×2 では左右・上下の隣が一致するので、隣は重複して 4 個（各 2 回）
#guard (List.finRange S2.n).all fun i => (S2.nbrs i).length == 4
#guard (Sim.make S3 (2/5)).D == 625

/-! ## 仕様の Metropolis 核 -/

-- 各行の和が 1
#guard (allConfigs S2.n).all fun σ =>
  ((allConfigs S2.n).map fun τ => kernel S2 (2/5) σ τ).sum == 1
-- 詳細釣り合い
#guard (allPairs S2.n).all fun (σ, τ) =>
  boltzmann S2 (2/5) σ * kernel S2 (2/5) σ τ == boltzmann S2 (2/5) τ * kernel S2 (2/5) τ σ
-- 定常性
#guard (allConfigs S2.n).all fun τ =>
  ((allConfigs S2.n).map fun σ => boltzmann S2 (2/5) σ * kernel S2 (2/5) σ τ).sum ==
    boltzmann S2 (2/5) τ
-- `Chain.pow` は遷移行列の積に一致する（2 ステップ）
#guard matrix (Chain.pow (kernel G3 (1/3)) 2) == matPow (matrix (kernel G3 (1/3))) 2
-- 6 ステップ（= 2n）ですべての成分が正（エルゴード性）
#guard (matPow (matrix (kernel G3 (1/3))) 6).all fun row => row.all (0 < ·)
#guard (matPow (matrix (kernel S2 (2/5))) 8).all fun row => row.all (0 < ·)
-- x = 1（無限温度）ではすべての反転が受理されるので周期 2：奇数ステップでは元に戻れない
#guard (List.range 8).all fun i => (matPow (matrix (kernel G3 1)) 3)[i]![i]! == 0

/-! ## 実装の厳密性 -/

-- 近傍だけで計算した受理確率 = 大域的な重みの比
#guard (allConfigs S3.n).all fun σ =>
  (List.finRange S3.n).all fun i => acceptLocal (2/5) (S3.nbrs i) σ i == accept S3 (2/5) σ i
-- 実装が引き起こす遷移確率 = 仕様の核（1 次元の環、x = 1/2、D = 2^2 = 4）
#guard (Sim.make G4 (1/2)).D == 4
#guard (allPairs G4.n).all fun (σ, τ) =>
  inducedKernel G4 (1/2) (Sim.make G4 (1/2)).D σ τ == kernel G4 (1/2) σ τ
#guard (allPairs G3.n).all fun (σ, τ) =>
  inducedKernel G3 (2/7) (Sim.make G3 (2/7)).D σ τ == kernel G3 (2/7) σ τ
-- 分母 D が足りないと（D = 7 では 4/49 を表せない）一致しない：厳密な一致には D の選び方が効いている
#guard !(allPairs G3.n).all fun (σ, τ) => inducedKernel G3 (2/7) 7 σ τ == kernel G3 (2/7) σ τ

/-! ## 乱数 -/

-- 棄却法：[M % m, M) の中で各剰余がちょうど M / m 回
#guard (List.range 7).all fun k =>
  (List.range' (100 % 7) (100 - 100 % 7)).countP (fun w => (w - 100 % 7) % 7 == k) == 100 / 7
-- u = k / D は [0, 1) の、分母が D を割り切る有理数
#guard
  let (us, _) := ((List.range 200).mapM fun _ => uniformRat 625).run (Rng.ofSeed 7)
  us.all fun u => 0 ≤ u && u < 1 && 625 % u.den == 0
-- 大きな m（2^64 を超える）でも範囲内
#guard
  let (ks, _) := ((List.range 50).mapM fun _ => uniformNat (3 ^ 50)).run (Rng.ofSeed 3)
  ks.all (· < 3 ^ 50)
-- 2^64 ちょうどの m（棄却なし）
#guard (Uniform.make (2 ^ 64)).lo == 0

/-! ## シミュレーションの再現性 -/

#guard
  let s := Sim.make S3 (2/5)
  if h : 0 < s.G.n then
    let ((_, st), _) := (s.run h (allUp s.G.n) 10 100).run (Rng.ofSeed 1)
    let ((_, st'), _) := (s.run h (allUp s.G.n) 10 100).run (Rng.ofSeed 1)
    st.samples == 100 && st.proposed == 900 && st.accepted == st'.accepted && st.sumE == st'.sumE
  else false

/-! ## 厳密解 -/

-- ヒストグラムから求めた ⟨E⟩ は、仕様の Boltzmann 分布で直接求めたものと一致
#guard
  let x : Rat := 2/5
  let direct := ((allConfigs S2.n).map fun σ => boltzmann S2 x σ * S2.energy σ).sum / S2.n
  (Exact.averages S2 x).e == direct

/-! ## 数値の表示 -/

#guard showDec (1/3) 4 == "0.3333"
#guard showDec (-2/3) 2 == "-0.67"
#guard showDec 2 3 == "2.000"
#guard parseRat "2.269" == some (2269/1000)
#guard parseRat "29/70" == some (29/70)
#guard parseRat "-1.5" == some (-3/2)
-- 臨界点 x_c = √2 - 1 の最良有理近似（70/169 は Pell 数の比、41/99 はその手前の中間近似分数）
#guard bestRational (sqrtApprox 2 - 1) 100 == 41/99
#guard bestRational (sqrtApprox 2 - 1) 200 == 70/169
#guard showDec (tOfX (70/169)) 3 == "2.269"
-- Boltzmann 因子は開区間 (0, 1) の中から選ぶ（端点 0, 1 に丸めない）
#guard bestRationalIn01 (1/10000) 200 == 1/200
#guard bestRationalIn01 (9999/10000) 200 == 199/200
#guard bestRationalIn01 (sqrtApprox 2 - 1) 200 == 70/169
#guard [1/10, 1, 10, 1000].all fun T => let x := xOfT T 100; 0 < x && x < 1
-- ln は 0 の近くでも正確（引数を [1/2, 1] に縮めてから級数を使う）
#guard showDec (lnApprox (1/1000)) 4 == "-6.9078"
#guard showDec (lnApprox (1/2981)) 4 == "-8.0000"
#guard showDec (lnApprox 2) 6 == "0.693147"
#guard closeRel (101/100) 1 (1/100) && !closeRel (102/100) 1 (1/100)

end LeanIsing.Tests
