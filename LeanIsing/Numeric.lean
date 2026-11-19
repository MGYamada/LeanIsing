import LeanIsing.Spec

/-!
# 表示用の数値計算（有理数だけで行う）

シミュレーションそのものは厳密な有理数だけで動く。ここにあるのは、入出力のための近似計算である。

* `showDec`：有理数を小数で表示する（四捨五入）。
* `expApprox` / `lnApprox`：温度 `T` と `x = exp(-2/T)` の換算用。テイラー級数を有理数で計算し、
  各ステップで `2^-128` 単位に丸める（浮動小数点数は使わない）。
* `bestRational`：分母に上限をつけた最良有理近似。温度 `T` から `x` を決めるのに使う。
* `onsagerM`：Onsager–Yang の自発磁化 `m(x) = (1 - sinh(2βJ)^(-4))^(1/8)`
  （無限に大きい正方格子での厳密解）。`sinh(2βJ) = (1/x - x)/2` なので、`x` から直接計算できる。
-/

namespace LeanIsing.Numeric

/-- `2^-128` 単位への切り捨て。 -/
def trunc (q : Rat) : Rat :=
  ((q * 2 ^ 128).floor : Rat) / 2 ^ 128

/-- 有理数を小数点以下 `d` 桁に四捨五入して表示する。 -/
def showDec (q : Rat) (d : Nat := 4) : String :=
  let neg := q < 0
  let a := if neg then -q else q
  let scale : Nat := 10 ^ d
  let r := (a * scale + 1 / 2).floor.toNat
  let ip := r / scale
  let fs := toString (r % scale)
  let fs := "".pushn '0' (d - fs.length) ++ fs
  (if neg && r != 0 then "-" else "") ++ toString ip ++ (if d == 0 then "" else "." ++ fs)

/-- `exp z`（`0 ≤ z ≤ 10` 程度）。 -/
def expApprox (z : Rat) : Rat := Id.run do
  let mut term : Rat := 1
  let mut sum : Rat := 1
  for k in [1:200] do
    term := trunc (term * z / k)
    sum := sum + term
  return sum

/-- `ln x`（`0 < x ≤ 1`）。`ln x = -2 artanh((1 - x)/(1 + x))`。 -/
def lnApprox (x : Rat) : Rat := Id.run do
  let y := trunc ((1 - x) / (1 + x))
  let y2 := trunc (y * y)
  let mut p := y
  let mut sum : Rat := 0
  for k in [0:2000] do
    sum := sum + trunc (p / (2 * k + 1))
    p := trunc (p * y2)
  return -2 * sum

/-- `r` に最も近い、分母が `qmax` 以下の有理数（最良有理近似）。 -/
def bestRational (r : Rat) (qmax : Nat) : Rat := Id.run do
  let mut best : Rat := (r + 1 / 2).floor
  let mut err : Rat := if best ≤ r then r - best else best - r
  for q in [1:qmax + 1] do
    let p := (r * q + 1 / 2).floor
    let c : Rat := (p : Rat) / q
    let e := if c ≤ r then r - c else c - r
    if e < err then
      best := c
      err := e
  return best

/-- 温度 `T` に対する `x = exp(-2/T)` の、分母 `qmax` 以下の最良有理近似。 -/
def xOfT (T : Rat) (qmax : Nat := 100) : Rat :=
  bestRational (1 / expApprox (2 / T)) qmax

/-- `x = exp(-2/T)` に対応する温度 `T = -2 / ln x`。 -/
def tOfX (x : Rat) : Rat := -2 / lnApprox x

/-- `tanh a`（`0 ≤ a`）。 -/
def tanhApprox (a : Rat) : Rat :=
  let e := expApprox (2 * a)
  (e - 1) / (e + 1)

/-- `artanh y = (1/2) ln((1 + y)/(1 - y))`（`0 ≤ y < 1`）。 -/
def artanhApprox (y : Rat) : Rat := -(lnApprox ((1 - y) / (1 + y))) / 2

/-- 非負の有理数の平方根（`2^-64` 単位）。 -/
def sqrtApprox (q : Rat) : Rat :=
  ((Nat.sqrt (q * 2 ^ 128).floor.toNat : Nat) : Rat) / 2 ^ 64

/-- Onsager–Yang の自発磁化（無限系、`T < T_c` すなわち `x < √2 - 1` で正、それ以外は 0）。 -/
def onsagerM (x : Rat) : Rat :=
  let s := (1 / x - x) / 2
  if s ≤ 1 then 0
  else sqrtApprox (sqrtApprox (sqrtApprox (1 - 1 / s ^ 4)))

/-- `"2.269"` や `"5/2"` や `"3"` を有理数として読む。 -/
def parseRat (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [a, b] => do
    let p ← a.trimAscii.toString.toInt?
    let q ← b.trimAscii.toString.toNat?
    if q == 0 then none else some ((p : Rat) / q)
  | [a] =>
    match a.splitOn "." with
    | [i] => (i.toInt?).map (fun n => (n : Rat))
    | [i, f] => do
      let neg := i.startsWith "-"
      let ip ← (if neg then (i.drop 1).toString else i).toNat?
      let fp ← f.toNat?
      let v : Rat := ip + (fp : Rat) / 10 ^ f.length
      some (if neg then -v else v)
    | _ => none
  | _ => none

end LeanIsing.Numeric
