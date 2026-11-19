import LeanIsing.Spec

/-!
# 小さな系の厳密解（全配位の和）

仕様の `allConfigs` で `2^n` 個の配位をすべて数え上げ、不満足ボンド数 `u` と `|M|` の同時ヒストグラム
（状態密度）を作る。`x` が有理数なら、熱平均 `⟨A⟩ = Σ A · x^u / Σ x^u` も厳密な有理数になる。
モンテカルロ法の結果を検証するのに使う（`lake exe ising --exact`）。
-/

namespace LeanIsing.Exact

/-- 熱平均（1 サイトあたり）。 -/
structure Averages where
  /-- `⟨E⟩ / n` -/
  e : Rat
  /-- `⟨|M|⟩ / n` -/
  absM : Rat
  /-- `⟨M²⟩ / n²` -/
  m2 : Rat
  /-- `⟨M⁴⟩ / n⁴` -/
  m4 : Rat

/-- `(u, |M|)` の同時ヒストグラム。添字は `u * (n + 1) + |M|`。 -/
def histogram (G : Graph) : Array Nat := Id.run do
  let B := G.bonds.length
  let mut h := Array.replicate ((B + 1) * (G.n + 1)) 0
  for σ in allConfigs G.n do
    let u := G.unsat σ
    let m := (G.magnetization σ).natAbs
    let k := u * (G.n + 1) + m
    h := h.modify k (· + 1)
  return h

/-- 厳密な熱平均。 -/
def averages (G : Graph) (x : Rat) : Averages := Id.run do
  let B := G.bonds.length
  let n := G.n
  let h := histogram G
  let mut z : Rat := 0
  let mut se : Rat := 0
  let mut sm : Rat := 0
  let mut sm2 : Rat := 0
  let mut sm4 : Rat := 0
  for u in [0:B + 1] do
    let w := x ^ u
    for m in [0:n + 1] do
      let c := h[u * (n + 1) + m]!
      if c != 0 then
        let cw := (c : Rat) * w
        z := z + cw
        se := se + cw * (2 * (u : Rat) - B)
        sm := sm + cw * m
        sm2 := sm2 + cw * (m : Rat) ^ 2
        sm4 := sm4 + cw * (m : Rat) ^ 4
  let nn : Rat := n
  return { e := se / z / nn, absM := sm / z / nn, m2 := sm2 / z / nn ^ 2, m4 := sm4 / z / nn ^ 4 }

end LeanIsing.Exact
