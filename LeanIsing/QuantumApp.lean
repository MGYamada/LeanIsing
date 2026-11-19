import LeanIsing.Layered
import LeanIsing.Quantum
import LeanIsing.QuantumExact
import LeanIsing.Lattice
import LeanIsing.App

/-!
# 横磁場 Ising 模型の量子モンテカルロ法（実行ファイルの `--quantum` モード）

空間グラフ `G`（既定は `N` サイトの環 = 1 次元横磁場 Ising 模型）について、Trotter 数 `M`、
逆温度 `β`（`J = 1`）、横磁場 `Γ` から `x = e^{-2β/M}`、`y = tanh(βΓ/M)` を有理数で決め、
2 層の模型 `trotter G M x y` を層つき模型の実行系（`Layered.Sim`）でシミュレーションする。

推定量（世界線の平均）：
* `⟨σᶻσᶻ⟩`：空間ボンドあたり `1 - 2 · (不満足な空間ボンドの割合)`。
* `⟨σˣ⟩`：虚時間ボンド `(i, τ)–(i, τ+1)` ごとに、同じ向きなら `y`、逆向きなら `1/y` の平均。
* `⟨|m_z|⟩`：世界線全体の磁化の絶対値（1 サイトあたり）。
* エネルギー `e = -(|bonds|/N) J_x ⟨σᶻσᶻ⟩ - Γ_y ⟨σˣ⟩`（`J_x = -ln x / (2ε)`、`Γ_y = artanh y / ε` は、
  有理数に丸めた `x`、`y` に厳密に対応する結合定数）。
-/

namespace LeanIsing.QuantumApp

open Numeric Rng Quantum App

structure Options where
  N : Nat := 16
  square : Option Nat := none
  M : Nat := 16
  beta : Rat := 4
  gammas : List Rat := [1/2, 4/5, 1, 6/5, 3/2, 2]
  therm : Nat := 500
  sweeps : Nat := 2000
  blocks : Nat := 20
  seed : Nat := 1
  qmax : Nat := 200
  exact : Bool := false
  help : Bool := false

def usage : String :=
"使い方: lake exe ising --quantum [オプション]

横磁場 Ising 模型 H = -Σ σᶻσᶻ - Γ Σ σˣ（J = 1）の経路積分量子モンテカルロ法（Suzuki–Trotter）。

  -N <整数>          1 次元の環のサイト数（既定 16）
  --square <整数>    空間格子を L×L の正方格子にする（2 次元横磁場 Ising 模型）
  -M <整数>          Trotter 数（虚時間のスライス数、既定 16）
  --beta <有理数>    逆温度 β（既定 4）
  --gamma <有理数,...>  横磁場 Γ（カンマ区切り、既定 0.5,0.8,1,1.2,1.5,2）
  --qmax <整数>      x = e^{-2β/M}, y = tanh(βΓ/M) を近似する有理数の分母の上限（既定 200）
  --therm <整数>     熱化のスイープ数（既定 500）
  --sweeps <整数>    測定のスイープ数（既定 2000）
  --blocks <整数>    誤差評価のブロック数（既定 20）
  --seed <整数>      乱数の seed（既定 1）
  --exact            同じ M での厳密値（2^N 次の転送行列の積）と比較する（空間サイト数 ≤ 6）
  -h, --help         この説明
"

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "-h" :: rest, o | "--help" :: rest, o => parseArgs rest { o with help := true }
  | "--exact" :: rest, o => parseArgs rest { o with exact := true }
  | "-N" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"-N の値が不正です: {v}"
    parseArgs rest { o with N := k }
  | "--square" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"--square の値が不正です: {v}"
    parseArgs rest { o with square := some k }
  | "-M" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"-M の値が不正です: {v}"
    parseArgs rest { o with M := k }
  | "--beta" :: v :: rest, o => do
    let some b := parseRat v | throw s!"--beta の値が不正です: {v}"
    unless 0 < b do throw "β は正でなければなりません"
    parseArgs rest { o with beta := b }
  | "--gamma" :: v :: rest, o => do
    let some gs := App.parseList v | throw s!"--gamma の値が不正です: {v}"
    unless gs.all (0 < ·) do throw "Γ は正でなければなりません"
    parseArgs rest { o with gammas := gs }
  | "--qmax" :: v :: rest, o => do
    let some k := v.toNat? | throw s!"--qmax の値が不正です: {v}"
    parseArgs rest { o with qmax := max 1 k }
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

/-- 1 ブロックの測定の合計。 -/
structure Acc where
  samples : Nat := 0
  zz : Rat := 0
  sx : Rat := 0
  absM : Rat := 0
  accepted : Nat := 0

structure Row where
  zz : Rat × Rat
  sx : Rat × Rat
  absM : Rat × Rat
  acc : Rat

/-- 1 つの `(x, y)` での量子モンテカルロ法。 -/
def simulate (o : Options) (G : Graph) (x y : Rat) (g : Rng) : Row × Rng := Id.run do
  let model := trotter G o.M x y
  let s := Layered.Sim.make model
  if h : 0 < s.M.n then
    let n : Rat := s.M.n
    let nb : Rat := (spaceBonds G o.M).length
    let nt : Rat := (timeBonds G.n o.M).length
    -- 熱化（全上向きから）
    let mut σ : Config s.M.n := allUp s.M.n
    let mut g := g
    for _ in [0:o.therm] do
      let ((σ', _), g') := (s.sweep h σ).run g
      σ := σ'
      g := g'
    let per := max 1 (o.sweeps / o.blocks)
    let mut zzs : Array Rat := #[]
    let mut sxs : Array Rat := #[]
    let mut ms : Array Rat := #[]
    let mut acc : Nat := 0
    for _ in [0:o.blocks] do
      let mut a : Acc := {}
      for _ in [0:per] do
        let ((σ', k), g') := (s.sweep h σ).run g
        σ := σ'
        g := g'
        let us : Rat := unsatOf (spaceBonds G o.M) σ
        let ut : Rat := unsatOf (timeBonds G.n o.M) σ
        let up : Rat := σ.toList.countP id
        let mz := (2 * up - n) / n
        a := { samples := a.samples + 1
               zz := a.zz + (1 - 2 * us / nb)
               sx := a.sx + ((nt - ut) * y + ut / y) / nt
               absM := a.absM + (if mz < 0 then -mz else mz)
               accepted := a.accepted + k }
      let k : Rat := a.samples
      zzs := zzs.push (a.zz / k)
      sxs := sxs.push (a.sx / k)
      ms := ms.push (a.absM / k)
      acc := acc + a.accepted
    let prop : Rat := (o.blocks * per : Nat) * n
    return ({ zz := meanErr zzs, sx := meanErr sxs, absM := meanErr ms, acc := (acc : Rat) / prop }, g)
  else
    return ({ zz := (0, 0), sx := (0, 0), absM := (0, 0), acc := 0 }, g)

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"エラー: {e}\n\n{usage}"; return 1
  if o.help then IO.println usage; return 0
  if o.M < 1 then IO.eprintln "エラー: M は 1 以上にしてください"; return 1
  let (G, desc) := match o.square with
    | some L => (Lattice.square L, s!"{L}×{L} 正方格子")
    | none => (Lattice.ring o.N, s!"{o.N} サイトの環")
  if G.n < 2 then IO.eprintln "エラー: 空間サイトは 2 個以上にしてください"; return 1
  if o.exact && G.n > 6 then IO.eprintln "エラー: --exact は空間サイト数 ≤ 6 のときだけ使えます"; return 1
  let eps := o.beta / o.M
  let x := bestRational (1 / expApprox (2 * eps)) o.qmax
  let Jx := -(lnApprox x) / (2 * eps)
  IO.println s!"LeanIsing — 横磁場 Ising 模型の経路積分量子モンテカルロ法（乱数・確率はすべて厳密有理数）"
  IO.println s!"空間格子 = {desc}、Trotter 数 M = {o.M}（世界線 {G.n * o.M} サイト）、β = {showDec o.beta 3}、\
    熱化 {o.therm} スイープ、測定 {o.sweeps} スイープ（{o.blocks} ブロック）、seed = {o.seed}"
  IO.println s!"x = e^(-2β/M) ≈ {x}（J_x = {showDec Jx 4}）、y = tanh(βΓ/M)。\
    Γ_y は y に厳密に対応する横磁場。受理判定は u = k/D（D = 受理確率の分母）との厳密比較。\n"
  let header :=
    s!"{padLeft "Γ" 6} {padRight "y" 11} {padLeft "Γ_y" 7}  {padLeft "⟨σᶻσᶻ⟩" 13} {padLeft "⟨σˣ⟩" 13} \
      {padLeft "⟨|m_z|⟩" 13} {padLeft "e" 8} {padLeft "受理率" 6}" ++
      (if o.exact then s!"  {padLeft "⟨σᶻσᶻ⟩ 厳密" 11} {padLeft "⟨σˣ⟩ 厳密" 10}" else "")
  IO.println header
  IO.println ("".pushn '-' (header.length + 4))
  let mut g := Rng.ofSeed o.seed
  for Γ in o.gammas do
    let t0 ← IO.monoMsNow
    let y := bestRational (tanhApprox (eps * Γ)) o.qmax
    let Γy := artanhApprox y / eps
    let (row, g') := simulate o G x y g
    g := g'
    let t1 ← IO.monoMsNow
    let bondsPerSite : Rat := (G.bonds.length : Rat) / G.n
    let e := -bondsPerSite * Jx * row.zz.1 - Γy * row.sx.1
    let mut line := s!"{padLeft (showDec Γ 3) 6} {padRight (toString y) 11} {padLeft (showDec Γy 4) 7}  \
      {padLeft (showME row.zz) 13} {padLeft (showME row.sx) 13} {padLeft (showME row.absM) 13} \
      {padLeft (showDec e 4) 8} {padLeft (showDec row.acc 3) 6}"
    if o.exact then
      let ex := QuantumExact.values G o.M x y
      line := line ++ s!"  {padLeft (showDec ex.zz 4) 11} {padLeft (showDec ex.sx 4) 10}"
    IO.println (line ++ s!"   [{t1 - t0} ms]")
  return 0

end LeanIsing.QuantumApp
