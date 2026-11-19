import LeanIsing

/-!
# 量子モンテカルロ法の単体テスト

小さな横磁場 Ising 模型で、証明が一般に保証していることを実際に計算して確かめる。
さらに、証明していない経路積分の恒等式 `Σ_世界線 Π_τ T(s_τ, s_{τ+1}) = Tr T^M` も数値的に確かめる。
-/

namespace LeanIsing.QuantumTests

open Quantum Layered

def R2 := Lattice.ring 2
def R3 := Lattice.ring 3

/-- 全配位の対。 -/
def allPairs (n : Nat) : List (Config n × Config n) :=
  (allConfigs n).flatMap fun σ => (allConfigs n).map fun τ => (σ, τ)

/-! ## 世界線の重みと 2 層の模型 -/

-- 2 層の模型の重み = Trotter 転送行列の要素の積
#guard (allConfigs (R3.n * 3)).all fun s =>
  (trotter R3 3 (2/5) (1/3)).weight s == pathWeight R3 3 (2/5) (1/3) s
-- M = 1 では古典模型の重み
#guard (allConfigs (R3.n * 1)).all fun s =>
  pathWeight R3 1 (2/5) (1/3) s == weight R3 (2/5) (slice s ⟨0, by decide⟩)
-- 経路積分の恒等式：Σ_世界線 Π_τ T(s_τ, s_{τ+1}) = Tr T^M（M = 1, 2, 3）
#guard [1, 2, 3].all fun M =>
  let T : QuantumExact.Mat := (allConfigs R3.n).toArray.map fun s =>
    (allConfigs R3.n).toArray.map fun s' => transfer R3 (2/5) (1/3) s s'
  ((allConfigs (R3.n * M)).map (pathWeight R3 M (2/5) (1/3))).sum ==
    QuantumExact.trace (QuantumExact.matPow T M)

/-! ## 実装の厳密性 -/

-- 層つき模型の局所的な受理確率 = 大域的な重みの比
#guard (allConfigs (R3.n * 2)).all fun σ =>
  (List.finRange (R3.n * 2)).all fun i =>
    acceptLocal (nbrLayers (trotter R3 2 (2/5) (1/3)) i) σ i ==
      acceptW (pathWeight R3 2 (2/5) (1/3)) σ i
-- 実装が引き起こす遷移確率 = 世界線の重みに対する Metropolis 核
#guard (allPairs (R2.n * 2)).all fun (σ, τ) =>
  Layered.inducedKernel (trotter R2 2 (1/2) (1/3)) σ τ ==
    metropolis (pathWeight R2 2 (1/2) (1/3)) σ τ
-- 世界線の分布は定常
#guard (allConfigs (R2.n * 2)).all fun τ =>
  ((allConfigs (R2.n * 2)).map fun σ =>
      pathDistribution R2 2 (1/2) (1/3) σ * metropolis (pathWeight R2 2 (1/2) (1/3)) σ τ).sum ==
    pathDistribution R2 2 (1/2) (1/3) τ

/-! ## 厳密値の計算 -/

-- 転送行列で求めた ⟨σᶻσᶻ⟩ と ⟨σˣ⟩ は、世界線の重みで直接平均したものと一致する
#guard
  let G := R3
  let M := 3
  let x : Rat := 2/5
  let y : Rat := 1/3
  let ws := (allConfigs (G.n * M)).map fun s => (s, pathWeight G M x y s)
  let Z := (ws.map (·.2)).sum
  let nb : Rat := (spaceBonds G M).length
  let nt : Rat := (timeBonds G.n M).length
  let zz := (ws.map fun (s, w) => w * (1 - 2 * (unsatOf (spaceBonds G M) s : Rat) / nb)).sum / Z
  let sx := (ws.map fun (s, w) =>
    let ut : Rat := unsatOf (timeBonds G.n M) s
    w * (((nt - ut) * y + ut / y) / nt)).sum / Z
  let ex := QuantumExact.values G M x y
  ex.zz == zz && ex.sx == sx

-- 乱数の前計算：UInt64 で求めた 2^64 % m は多倍長で求めたものと一致する
#guard [1, 2, 3, 7, 625, 10 ^ 12, 2 ^ 63 + 5, 2 ^ 64 - 1].all fun m =>
  (Rng.Uniform.make m).lo == 2 ^ 64 % m

end LeanIsing.QuantumTests
