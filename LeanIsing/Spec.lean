/-!
# Ising 模型と Metropolis 法の仕様（信頼の核）

このファイルだけを読めば、証明した定理（`Proofs/`）が何を主張しているかがわかるように書いてある。
シミュレーションの実行系（`LeanIsing.Engine`）が実際に動かしているマルコフ連鎖が、
ここで定める遷移確率 `kernel` と**厳密に一致する**ことは `Proofs.Exactness` で証明する。

* 依存するのは Lean core の `Nat`、`Rat`（厳密な有理数）、`List`、`Vector` だけ。
* 浮動小数点数は一切使わない。確率はすべて `Rat` で表す。

## 温度の表し方

強磁性 Ising 模型 `E(σ) = -J Σ_{⟨ij⟩} s_i s_j`（`J > 0`）の Boltzmann 重みは

  `exp(-β E(σ)) = exp(β J |bonds|) · x ^ (不満足ボンドの数)`、 `x = exp(-2βJ) ∈ (0, 1)`

と書ける（`s_i s_j = 1 - 2·[s_i ≠ s_j]` だから）。定数倍は確率に効かないので、
重みは `x ^ unsat σ` でよい。そこで温度を `β` ではなく**有理数 `x` で指定する**ことにすると、
Boltzmann 重みも Metropolis の受理確率もすべて厳密な有理数になる。
（例：臨界点は `x_c = √2 - 1 = 0.41421…`。`T = -2J / ln x`。）
-/

namespace LeanIsing

/-- 相互作用グラフ。サイトは `Fin n`、ボンド（相互作用する 2 サイトの組）はリストで与える。
自己ループ `(i, i)` や多重ボンドがあってもよい（自己ループは常に満足されるので何もしない）。 -/
structure Graph where
  n : Nat
  bonds : List (Fin n × Fin n)

/-- スピン配位：`true` が上向き（+1）、`false` が下向き（-1）。 -/
abbrev Config (n : Nat) := Vector Bool n

/-- サイト `i` のスピンを反転した配位。Metropolis 法の提案はこれだけである。 -/
def flip {n : Nat} (σ : Config n) (i : Fin n) : Config n :=
  σ.set i (!σ[i])

/-- すべて上向きの配位。 -/
def allUp (n : Nat) : Config n := Vector.replicate n true

/-- すべての配位（`2 ^ n` 個）を並べたリスト。和 `Σ_σ` はこのリストの上でとる。 -/
def allConfigs : (n : Nat) → List (Config n)
  | 0 => [#v[]]
  | n + 1 => (allConfigs n).flatMap fun v => [v.push false, v.push true]

namespace Graph

variable (G : Graph)

/-- 不満足ボンド（両端のスピンが逆向きのボンド）の数。 -/
def unsat (σ : Config G.n) : Nat :=
  G.bonds.countP fun b => σ[b.1] != σ[b.2]

/-- エネルギー `E(σ) = -Σ_{⟨ij⟩} s_i s_j = 2 · unsat σ - |bonds|`（`J = 1` 単位）。 -/
def energy (σ : Config G.n) : Int :=
  2 * (G.unsat σ : Int) - G.bonds.length

/-- 磁化 `M(σ) = Σ_i s_i = 2 · (上向きの数) - n`。 -/
def magnetization (σ : Config G.n) : Int :=
  2 * (σ.toList.countP id : Int) - G.n

end Graph

/-! ## 一般の重みに対する Metropolis 法

正の重み `w : Config n → Rat` に対して、規格化した分布 `w / Σ w` と、単一スピン反転の
Metropolis 核を定義する。古典 Ising 模型の重み `x ^ unsat σ` も、横磁場 Ising 模型の
経路積分（世界線）表示の重みも、この形で扱う。 -/

/-- 規格化した分布 `π(σ) = w(σ) / Σ_σ w(σ)`。 -/
def normalize {n : Nat} (w : Config n → Rat) (σ : Config n) : Rat :=
  w σ / ((allConfigs n).map w).sum

/-- Metropolis の受理確率 `min(1, w(σ') / w(σ))`（`σ'` はサイト `i` を反転した配位）。 -/
def acceptW {n : Nat} (w : Config n → Rat) (σ : Config n) (i : Fin n) : Rat :=
  min 1 (w (flip σ i) / w σ)

/-- 重み `w` に対する Metropolis 法の 1 ステップの遷移確率 `P(σ → τ)`。

サイト `i` を確率 `1/n` で一様に選び、確率 `acceptW w σ i` で反転を受理して `flip σ i` へ移り、
確率 `1 - acceptW w σ i` で棄却して `σ` にとどまる。 -/
def metropolis {n : Nat} (w : Config n → Rat) (σ τ : Config n) : Rat :=
  ((List.finRange n).map fun i =>
      (if flip σ i = τ then acceptW w σ i else 0) +
      (if σ = τ then 1 - acceptW w σ i else 0)).sum / n

/-! ## 古典 Ising 模型の Boltzmann 分布と Metropolis 法 -/

/-- 規格化前の Boltzmann 重み `x ^ unsat σ`（`exp(-βE)` に比例）。 -/
def weight (G : Graph) (x : Rat) (σ : Config G.n) : Rat :=
  x ^ G.unsat σ

/-- 分配関数 `Z = Σ_σ x ^ unsat σ`。 -/
def partition (G : Graph) (x : Rat) : Rat :=
  ((allConfigs G.n).map (weight G x)).sum

/-- Boltzmann 分布 `π(σ) = x ^ unsat σ / Z`。 -/
def boltzmann (G : Graph) (x : Rat) : Config G.n → Rat :=
  normalize (weight G x)

/-- Metropolis の受理確率 `min(1, π(σ') / π(σ))`。 -/
def accept (G : Graph) (x : Rat) : Config G.n → Fin G.n → Rat :=
  acceptW (weight G x)

/-- 古典 Ising 模型の Metropolis 法の遷移確率。 -/
def kernel (G : Graph) (x : Rat) : Config G.n → Config G.n → Rat :=
  metropolis (weight G x)

/-! ## 異方的な Ising 模型（ボンドの層ごとの Boltzmann 因子）

ボンドを種類（層）ごとに分け、層 `l` の不満足ボンド 1 本ごとに因子 `x_l = exp(-2βJ_l)` を掛ける。
横磁場 Ising 模型の経路積分表示は、空間方向の層（`x = exp(-2βJ/M)`）と虚時間方向の層
（`y = tanh(βΓ/M)`）の 2 層をもつ模型になる（`LeanIsing.Quantum`）。古典模型は 1 層の場合である。 -/

/-- ボンドの集合 `bs` のうち、両端のスピンが逆向きのものの数。 -/
def unsatOf {n : Nat} (bs : List (Fin n × Fin n)) (σ : Config n) : Nat :=
  bs.countP fun b => σ[b.1] != σ[b.2]

/-- 異方的な Ising 模型：同じサイトの上に、ボンドの層 `(bs_l, x_l)` を並べたもの。 -/
structure Model where
  n : Nat
  layers : List (List (Fin n × Fin n) × Rat)

/-- 層ごとの因子の積 `Π_l x_l ^ unsatOf bs_l σ`。 -/
def layerWeight {n : Nat} (σ : Config n) : List (List (Fin n × Fin n) × Rat) → Rat
  | [] => 1
  | l :: rest => l.2 ^ unsatOf l.1 σ * layerWeight σ rest

namespace Model

variable (M : Model)

/-- 規格化前の Boltzmann 重み `w(σ) = Π_l x_l ^ (層 l の不満足ボンド数)`。 -/
def weight (σ : Config M.n) : Rat := layerWeight σ M.layers

/-- Boltzmann 分布 `w / Σ w`。 -/
def boltzmann : Config M.n → Rat := normalize M.weight

/-- Metropolis 法の遷移確率。 -/
def kernel : Config M.n → Config M.n → Rat := metropolis M.weight

/-- すべての因子が `0 < x_l ≤ 1`（強磁性で温度が正）。 -/
def Valid : Prop := ∀ l ∈ M.layers, 0 < l.2 ∧ l.2 ≤ 1

/-- 因子が 1 未満の層に、自己ループでないボンドがある（どこかで反転が棄却されうる）。 -/
def Frustratable : Prop := ∃ l ∈ M.layers, l.2 < 1 ∧ ∃ b ∈ l.1, b.1 ≠ b.2

end Model

/-- 古典模型を 1 層の模型として見る。 -/
def Graph.toModel (G : Graph) (x : Rat) : Model := ⟨G.n, [(G.bonds, x)]⟩

/-! ## マルコフ連鎖の性質

一般の遷移行列 `P : Config n → Config n → Rat` について定義する。
仕様の Metropolis 核 `metropolis w`（`kernel G x` など）にも、実装が実際に動かしている連鎖の遷移確率
（`Engine.inducedKernel`）にも同じ定義を当てはめる。 -/

namespace Chain

variable {n : Nat}

/-- 遷移行列の `m` 乗 `P^m(σ → τ)`（`m` ステップの遷移確率）。 -/
def pow (P : Config n → Config n → Rat) : Nat → Config n → Config n → Rat
  | 0, σ, τ => if σ = τ then 1 else 0
  | m + 1, σ, τ => ((allConfigs n).map fun ρ => P σ ρ * pow P m ρ τ).sum

/-- 確率行列であること：成分が非負で、各行の和が 1。 -/
def Stochastic (P : Config n → Config n → Rat) : Prop :=
  (∀ σ τ, 0 ≤ P σ τ) ∧ ∀ σ, ((allConfigs n).map fun τ => P σ τ).sum = 1

/-- 詳細釣り合い：`π(σ) P(σ → τ) = π(τ) P(τ → σ)`。 -/
def DetailedBalance (π : Config n → Rat) (P : Config n → Config n → Rat) : Prop :=
  ∀ σ τ, π σ * P σ τ = π τ * P τ σ

/-- 定常性：`Σ_σ π(σ) P(σ → τ) = π(τ)`。 -/
def Stationary (π : Config n → Rat) (P : Config n → Config n → Rat) : Prop :=
  ∀ τ, ((allConfigs n).map fun σ => π σ * P σ τ).sum = π τ

/-- 既約性：どの配位からどの配位へも、有限ステップで正の確率で移れる。 -/
def Irreducible (P : Config n → Config n → Rat) : Prop :=
  ∀ σ τ, ∃ m, 0 < pow P m σ τ

/-- エルゴード性（有限状態の連鎖としての正則性 = 既約かつ非周期的）：
あるステップ数 `m` があって、どの配位からどの配位へもちょうど `m` ステップで正の確率で移れる。
有限状態マルコフ連鎖では、これと定常分布の存在から、定常分布の一意性と、
任意の初期分布からの定常分布への収束が従う（Perron–Frobenius）。 -/
def Ergodic (P : Config n → Config n → Rat) : Prop :=
  ∃ m, ∀ σ τ, 0 < pow P m σ τ

/-! ### 収束 -/

/-- 確率分布：非負で総和が 1。 -/
def IsDistribution (μ : Config n → Rat) : Prop :=
  (∀ σ, 0 ≤ μ σ) ∧ ((allConfigs n).map μ).sum = 1

/-- 分布 `μ` から `t` ステップ後の分布 `μP^t`、すなわち `(μP^t)(τ) = Σ_σ μ(σ) P^t(σ → τ)`。 -/
def evolve (P : Config n → Config n → Rat) (μ : Config n → Rat) (t : Nat) (τ : Config n) : Rat :=
  ((allConfigs n).map fun σ => μ σ * pow P t σ τ).sum

/-- 有理数の絶対値。 -/
def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- 2 つの分布の L¹ 距離 `Σ_τ |μ(τ) - ν(τ)|`（全変動距離の 2 倍）。 -/
def l1Dist (μ ν : Config n → Rat) : Rat :=
  ((allConfigs n).map fun τ => absQ (μ τ - ν τ)).sum

/-- 収束：任意の初期分布 `μ` について、`t` ステップ後の分布 `μP^t` は `t → ∞` で `π` に収束する。
（どの `ε > 0` に対しても、十分大きなすべての `t` で、すべての配位 `τ` について `|μP^t(τ) - π(τ)| < ε`。） -/
def Converges (π : Config n → Rat) (P : Config n → Config n → Rat) : Prop :=
  ∀ μ, IsDistribution μ → ∀ ε : Rat, 0 < ε → ∃ T : Nat, ∀ t, T ≤ t → ∀ τ,
    π τ - ε < evolve P μ t τ ∧ evolve P μ t τ < π τ + ε

/-- 幾何収束：ある `m > 0` と `0 ≤ ρ < 1` があって、任意の初期分布 `μ` と任意の `t` について
`Σ_τ |μP^t(τ) - π(τ)| ≤ 2 ρ^⌊t/m⌋`。初期分布によらない一様な指数的収束である。 -/
def GeometricConvergence (π : Config n → Rat) (P : Config n → Config n → Rat) : Prop :=
  ∃ m : Nat, 0 < m ∧ ∃ ρ : Rat, 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ μ, IsDistribution μ → ∀ t, l1Dist (evolve P μ t) π ≤ 2 * ρ ^ (t / m)

end Chain

end LeanIsing
