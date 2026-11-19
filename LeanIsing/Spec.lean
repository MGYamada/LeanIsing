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

/-! ## Boltzmann 分布 -/

/-- 規格化前の Boltzmann 重み `x ^ unsat σ`（`exp(-βE)` に比例）。 -/
def weight (G : Graph) (x : Rat) (σ : Config G.n) : Rat :=
  x ^ G.unsat σ

/-- 分配関数 `Z = Σ_σ x ^ unsat σ`。 -/
def partition (G : Graph) (x : Rat) : Rat :=
  ((allConfigs G.n).map (weight G x)).sum

/-- Boltzmann 分布 `π(σ) = x ^ unsat σ / Z`。 -/
def boltzmann (G : Graph) (x : Rat) (σ : Config G.n) : Rat :=
  weight G x σ / partition G x

/-! ## Metropolis 法 -/

/-- Metropolis の受理確率 `min(1, π(σ') / π(σ))`（`σ'` はサイト `i` を反転した配位）。 -/
def accept (G : Graph) (x : Rat) (σ : Config G.n) (i : Fin G.n) : Rat :=
  min 1 (weight G x (flip σ i) / weight G x σ)

/-- Metropolis 法の 1 ステップの遷移確率 `P(σ → τ)`。

サイト `i` を確率 `1/n` で一様に選び、確率 `accept σ i` で反転を受理して `flip σ i` へ移り、
確率 `1 - accept σ i` で棄却して `σ` にとどまる。 -/
def kernel (G : Graph) (x : Rat) (σ τ : Config G.n) : Rat :=
  ((List.finRange G.n).map fun i =>
      (if flip σ i = τ then accept G x σ i else 0) +
      (if σ = τ then 1 - accept G x σ i else 0)).sum / G.n

/-! ## マルコフ連鎖の性質

一般の遷移行列 `P : Config n → Config n → Rat` について定義する。
仕様の Metropolis 核 `kernel G x` にも、実装が実際に動かしている連鎖の遷移確率
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

end Chain

end LeanIsing
