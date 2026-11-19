import LeanIsing.Engine
import LeanIsing.Lattice
import LeanIsing.Numeric
import LeanIsing.Exact

/-!
# シミュレーションの実行ファイル

`L × L` 正方格子（周期境界）の Ising 模型を、温度ごとに Metropolis 法でシミュレーションし、
1 サイトあたりのエネルギー `⟨e⟩`、磁化の絶対値 `⟨|m|⟩`、Binder 比 `U₄ = 1 - ⟨m⁴⟩ / (3⟨m²⟩²)`、
受理率を表示する。誤差は測定をブロックに分けた平均のばらつき（標準誤差）。
-/

namespace LeanIsing.App

open Engine Numeric Rng

structure Options where
  L : Nat := 24
  temps : List Rat := [3/2, 2, 22/10, 2269/1000, 235/100, 25/10, 3, 35/10]
  xs : Option (List Rat) := none
  therm : Nat := 500
  sweeps : Nat := 2000
  blocks : Nat := 20
  seed : Nat := 1
  hot : Bool := false
  showLattice : Bool := false
  exact : Bool := false
  qmax : Nat := 100
  help : Bool := false

def usage : String :=
"使い方: lake exe ising [オプション]

  -L <整数>          格子の一辺（既定 24。L×L 周期境界）
  -T <温度,...>      温度 T（J = k_B = 1）。カンマ区切りで複数可。例: -T 2.0,2.269,2.5
                     x = exp(-2/T) の、分母 --qmax 以下の最良有理近似を使う
  -x <有理数,...>    温度を x = exp(-2/T) で直接指定（0 < x < 1）。例: -x 29/70,2/5
  --qmax <整数>      -T から x を作るときの分母の上限（既定 100）
  --therm <整数>     熱化のスイープ数（既定 500）
  --sweeps <整数>    測定のスイープ数（既定 2000）
  --blocks <整数>    誤差評価のブロック数（既定 20）
  --seed <整数>      乱数の seed（既定 1）
  --hot              ランダムな配位から始める（既定は全上向き）
  --show             最終配位を表示する
  --exact            全配位の和による厳密解と比較する（L ≤ 4）
  --quantum          横磁場 Ising 模型の量子モンテカルロ法（lake exe ising --quantum --help）
  -h, --help         この説明
"

def parseList (s : String) : Option (List Rat) :=
  (s.splitOn ",").mapM fun t => parseRat t

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "-h" :: rest, o | "--help" :: rest, o => parseArgs rest { o with help := true }
  | "--hot" :: rest, o => parseArgs rest { o with hot := true }
  | "--show" :: rest, o => parseArgs rest { o with showLattice := true }
  | "--exact" :: rest, o => parseArgs rest { o with exact := true }
  | "-L" :: v :: rest, o => do
    let some L := v.toNat? | throw s!"-L の値が不正です: {v}"
    parseArgs rest { o with L }
  | "-T" :: v :: rest, o => do
    let some ts := parseList v | throw s!"-T の値が不正です: {v}"
    unless ts.all (0 < ·) do throw "温度は正でなければなりません"
    parseArgs rest { o with temps := ts, xs := none }
  | "-x" :: v :: rest, o => do
    let some xs := parseList v | throw s!"-x の値が不正です: {v}"
    unless xs.all (fun x => 0 < x && x < 1) do throw "x は 0 < x < 1 でなければなりません"
    parseArgs rest { o with xs := some xs }
  | "--qmax" :: v :: rest, o => do
    let some q := v.toNat? | throw s!"--qmax の値が不正です: {v}"
    parseArgs rest { o with qmax := max 1 q }
  | "--therm" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"--therm の値が不正です: {v}"
    parseArgs rest { o with therm := k }
  | "--sweeps" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"--sweeps の値が不正です: {v}"
    parseArgs rest { o with sweeps := k }
  | "--blocks" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"--blocks の値が不正です: {v}"
    parseArgs rest { o with blocks := max 1 k }
  | "--seed" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"--seed の値が不正です: {v}"
    parseArgs rest { o with seed := k }
  | a :: _, _ => throw s!"不明な引数です: {a}"

def padLeft (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s
def padRight (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

/-- ブロックごとの平均の列から、平均と標準誤差。 -/
def meanErr (xs : Array Rat) : Rat × Rat :=
  let k := xs.size
  if k == 0 then (0, 0) else
  let mean : Rat := xs.foldl (· + ·) (0 : Rat) / (k : Rat)
  if k == 1 then (mean, 0) else
  let var : Rat := xs.foldl (fun s v => s + (v - mean) ^ 2) (0 : Rat) / ((k - 1 : Nat) : Rat)
  (mean, sqrtApprox (var / (k : Rat)))

/-- 平均 ± 誤差の表示（誤差は 1 桁目まで）。 -/
def showME (me : Rat × Rat) (d : Nat := 4) : String :=
  s!"{showDec me.1 d}({padLeft (showDec (me.2 * 10 ^ d) 0) 1})"

/-- 配位を文字で描く（上向き `█`、下向き `·`）。 -/
def render {n : Nat} (L : Nat) (σ : Config n) : String := Id.run do
  let mut out := ""
  for r in [0:L] do
    let mut line := "  "
    for c in [0:L] do
      line := line ++ (if σ.toArray[r * L + c]?.getD false then "█" else "·")
    out := out ++ line ++ "\n"
  return out

structure Row where
  e : Rat × Rat
  absM : Rat × Rat
  m2 : Rat
  m4 : Rat
  acc : Rat

/-- 1 つの温度でのシミュレーション。 -/
def simulate (o : Options) (x : Rat) (g : Rng) : Row × Rng × Option String := Id.run do
  let G := Lattice.square o.L
  let s := Sim.make G x
  if h : 0 < s.G.n then
    let n : Rat := s.G.n
    let (σ0, g) := (if o.hot then randomConfig s.G.n else pure (allUp s.G.n)).run g
    let ((σ, _), g) := (s.run h σ0 o.therm 0).run g
    let per := max 1 (o.sweeps / o.blocks)
    let mut σ := σ
    let mut g := g
    let mut es : Array Rat := #[]
    let mut ms : Array Rat := #[]
    let mut sm2 : Rat := 0
    let mut sm4 : Rat := 0
    let mut acc : Nat := 0
    let mut prop : Nat := 0
    for _ in [0:o.blocks] do
      let ((σ', st), g') := (s.run h σ 0 per).run g
      σ := σ'
      g := g'
      let k : Rat := st.samples
      es := es.push ((st.sumE : Rat) / k / n)
      ms := ms.push ((st.sumAbsM : Rat) / k / n)
      sm2 := sm2 + (st.sumM2 : Rat) / k / n ^ 2
      sm4 := sm4 + (st.sumM4 : Rat) / k / n ^ 4
      acc := acc + st.accepted
      prop := prop + st.proposed
    let b : Rat := o.blocks
    let row : Row := { e := meanErr es, absM := meanErr ms, m2 := sm2 / b, m4 := sm4 / b,
                       acc := if prop == 0 then 0 else (acc : Rat) / prop }
    return (row, g, if o.showLattice then some (render o.L σ) else none)
  else
    return ({ e := (0, 0), absM := (0, 0), m2 := 0, m4 := 0, acc := 0 }, g, none)

def binder (m2 m4 : Rat) : Rat := if m2 == 0 then 0 else 1 - m4 / (3 * m2 ^ 2)

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"エラー: {e}\n\n{usage}"; return 1
  if o.help then IO.println usage; return 0
  if o.L < 2 then IO.eprintln "エラー: L は 2 以上にしてください"; return 1
  if o.exact && o.L > 4 then IO.eprintln "エラー: --exact は L ≤ 4 のときだけ使えます"; return 1
  let points : List (Option Rat × Rat) := match o.xs with
    | some xs => xs.map fun x => (none, x)
    | none => o.temps.map fun T => (some T, xOfT T o.qmax)
  -- x は開区間 (0, 1) の中から選ぶ。丸めで温度が 1% 以上ずれるなら止める
  for (T?, x) in points do
    if let some T := T? then
      unless closeRel (tOfX x) T (1 / 100) do
        IO.eprintln s!"エラー: T = {showDec T 4} の x = exp(-2/T) を分母 {o.qmax} 以下の有理数で表すと \
          {x}（T_x = {showDec (tOfX x) 4}）になり、T から 1% 以上ずれます。--qmax を大きくしてください。"
        return 1
  let G := Lattice.square o.L
  IO.println s!"LeanIsing — 2 次元 Ising 模型の Metropolis 法（乱数・確率はすべて厳密有理数）"
  IO.println s!"L = {o.L}（{G.n} サイト、周期境界）、熱化 {o.therm} スイープ、\
    測定 {o.sweeps} スイープ（{o.blocks} ブロック）、seed = {o.seed}、\
    初期配位 = {if o.hot then "ランダム" else "全上向き"}"
  IO.println s!"x = exp(-2/T)。乱数 u = k/D（D = x の分母 ^ 4）との厳密比較で受理する。\
    T_x は x に対応する温度、m_∞ は無限系の厳密解（Onsager–Yang）。\n"
  let header :=
    s!"{padLeft "T" 7} {padRight "x" 11} {padLeft "T_x" 7} {padLeft "D" 10}  \
      {padLeft "⟨e⟩" 13} {padLeft "⟨|m|⟩" 13}  {padLeft "U₄" 6} {padLeft "受理率" 6}  {padLeft "m_∞" 6}" ++
      (if o.exact then s!"  {padLeft "⟨e⟩ 厳密" 9} {padLeft "⟨|m|⟩ 厳密" 9}" else "")
  IO.println header
  IO.println ("".pushn '-' (header.length + 4))
  let mut g := Rng.ofSeed o.seed
  for (T?, x) in points do
    let t0 ← IO.monoMsNow
    let (row, g', pic) := simulate o x g
    g := g'
    let t1 ← IO.monoMsNow
    let s := Sim.make G x
    let Tcol := match T? with | some T => showDec T 4 | none => "-"
    let Dcol := s!"{x.den}^{maxLen s.nbrTable}"
    let mut line := s!"{padLeft Tcol 7} {padRight (toString x) 11} {padLeft (showDec (tOfX x) 4) 7} \
      {padLeft Dcol 10}  {padLeft (showME row.e) 13} {padLeft (showME row.absM) 13}  \
      {padLeft (showDec (binder row.m2 row.m4) 3) 6} {padLeft (showDec row.acc 3) 6}  \
      {padLeft (showDec (onsagerM x) 3) 6}"
    if o.exact then
      let ex := Exact.averages G x
      line := line ++ s!"  {padLeft (showDec ex.e 4) 9} {padLeft (showDec ex.absM 4) 9}"
    IO.println (line ++ s!"   [{t1 - t0} ms]")
    if let some p := pic then IO.println p
  return 0

end LeanIsing.App
