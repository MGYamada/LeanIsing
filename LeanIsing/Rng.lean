/-!
# 厳密有理数の一様乱数

* 64 ビット擬似乱数の源には SplitMix64 を使う（seed を固定すれば、どの環境でも同じ列になる）。
* そこから棄却法で `[0, m)` 上の**偏りのない**整数一様乱数 `Uniform.sample` を作り、
* 一様乱数 `u = k / D`（`k ∈ {0, 1, …, D - 1}`）を**厳密な有理数 `Rat`** として返す（`uniformRat`）。

浮動小数点数は使わない。Metropolis 法の受理判定 `u < min(1, x^Δ)` も `Rat` の厳密な比較で行う。

## 棄却法が偏らないこと

64 ビット語を `c` 個つないだ `w ∈ [0, 2^(64c))` を引き、`w ≥ lo`（`lo = 2^(64c) % m`）のときだけ
採用して `(w - lo) % m` を返す（それ以外は引き直す）。採用された `w` に対して `w - lo` は
`[0, m · ⌊2^(64c) / m⌋)` を動き、その中で各剰余 `k ∈ [0, m)` はちょうど `⌊2^(64c) / m⌋` 回ずつ現れる
（`Proofs.Theorems.rejection_exact`）ので、源が理想的な一様乱数なら、出力は `[0, m)` 上の
厳密な一様分布になる。
-/

namespace LeanIsing.Rng

/-- SplitMix64 の状態。 -/
structure Rng where
  state : UInt64
  deriving Inhabited, Repr

/-- SplitMix64 の 1 ステップ。 -/
def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- seed から乱数生成器を作る。 -/
def Rng.ofSeed (seed : Nat) : Rng := ⟨seed.toUInt64⟩

abbrev RandM := StateM Rng

/-- 64 ビット語を 1 個引く。 -/
def word64 : RandM UInt64 := do
  let (w, g) := (← get).next
  set g
  return w

/-- 64 ビット語を `c` 個つないだ `[0, 2^(64c))` の一様乱数。 -/
def words : Nat → RandM Nat
  | 0 => pure 0
  | c + 1 => do
    let hi ← words c
    let lo ← word64
    return hi * 2 ^ 64 + lo.toNat

/-- `[0, m)` の一様乱数を引くための前計算。
64 ビット語を `c` 個つないだ `w ∈ [0, 2^(64c))` のうち `w ≥ lo`（`lo = 2^(64c) % m`）だけを採用し、
`(w - lo) % m` を返す。 -/
structure Uniform where
  m : Nat
  c : Nat
  lo : Nat
  deriving Repr, Inhabited

/-- `m < 2^64` なら 64 ビット語 1 個（棄却確率 `< m / 2^64`）、それより大きければ
`2^(64c) ≥ 2^32 · m` となる語数 `c`（棄却確率 `< 2^-32`）を使う。 -/
def Uniform.make (m : Nat) : Uniform :=
  if m.log2 < 64 then
    -- `m < 2^64` なので `2^64 % m = (2^64 - m) % m` を `UInt64` で計算できる（多倍長演算を避ける）
    let m64 := m.toUInt64
    { m, c := 1, lo := ((0 - m64) % m64).toNat }
  else
    let c := (m.log2 + 32) / 64 + 1
    { m, c, lo := 2 ^ (64 * c) % m }

/-- 棄却法の本体（64 ビット語 1 個の場合。`UInt64` だけで計算する）。 -/
partial def rejectLoop64 (m lo : UInt64) : RandM UInt64 := do
  let w ← word64
  if lo ≤ w then return (w - lo) % m else rejectLoop64 m lo

/-- 棄却法の本体（一般の場合）。 -/
partial def rejectLoop (m c lo : Nat) : RandM Nat := do
  let w ← words c
  if lo ≤ w then return (w - lo) % m else rejectLoop m c lo

/-- `[0, m)` 上の一様乱数（棄却法なので偏りがない）。`m ≤ 1` なら乱数を消費せずに 0 を返す。 -/
def Uniform.sample (U : Uniform) : RandM Nat :=
  if U.m ≤ 1 then pure 0
  else if U.c = 1 then return (← rejectLoop64 U.m.toUInt64 U.lo.toUInt64).toNat
  else rejectLoop U.m U.c U.lo

/-- `[0, m)` 上の一様乱数。 -/
def uniformNat (m : Nat) : RandM Nat := (Uniform.make m).sample

/-- 厳密有理数の一様乱数 `u = k / D`（`k` は `{0, 1, …, D - 1}` 上で一様）。`0 ≤ u < 1`。
`mkRat k D` は `(k : Rat) / D` に等しい（`Rat.mkRat_eq_div`）。 -/
def uniformRat (D : Nat) : RandM Rat := do
  let k ← uniformNat D
  return mkRat k D

end LeanIsing.Rng
