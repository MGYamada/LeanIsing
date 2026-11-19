import Proofs.Ergodicity

/-!
# 定常分布への収束

有限状態のマルコフ連鎖について、Perron–Frobenius の定理を使わずに、Doeblin の議論で
定常分布への幾何収束を証明する。

* `P` が確率行列で、`π` が定常分布、ある `m > 0` で `P^m` の全成分が正なら、
  全成分の下界 `δ > 0` がとれる。和が 0 のベクトル `v` について
  `Σ_τ |(vP^m)(τ)| ≤ (1 - Nδ) Σ_σ |v(σ)|`（`N` は配位の数）が成り立つ（`l1_contract`）。
  `(vP^m)(τ) = Σ_σ v(σ) (P^m(σ → τ) - δ)` と書き直して三角不等式を使うだけである。
* `v = μP^t - π` は和が 0 で、`μP^(t+m) - π = (μP^t - π) P^m` なので、`m` ステップごとに
  L¹ 距離が `ρ = 1 - Nδ < 1` 倍以下に縮む。よって `Σ_τ |μP^t(τ) - π(τ)| ≤ 2 ρ^⌊t/m⌋`
  （`geometric_of_primitive`）。
* `ρ^k → 0` は Bernoulli の不等式 `ρ^k (1 + k(1 - ρ)) ≤ 1` から従う（`converges_of_geometric`）。

最後に Metropolis 核に当てはめる（`metropolis_geometric`、`metropolis_converges`）。
-/

namespace LeanIsing.Proofs

open Chain

/-! ## 絶対値 -/

theorem rat_le_of_eq {a b : Rat} (h : a = b) : a ≤ b := h ▸ Rat.le_refl

theorem absQ_nonneg (q : Rat) : 0 ≤ absQ q := by
  unfold absQ; split <;> grind

theorem le_absQ (q : Rat) : q ≤ absQ q := by
  unfold absQ; split <;> grind

theorem neg_le_absQ (q : Rat) : -q ≤ absQ q := by
  unfold absQ; split <;> grind

theorem absQ_le {q c : Rat} (h₁ : q ≤ c) (h₂ : -q ≤ c) : absQ q ≤ c := by
  unfold absQ; split <;> grind

theorem absQ_add_le (a b : Rat) : absQ (a + b) ≤ absQ a + absQ b := by
  have := le_absQ a; have := le_absQ b; have := neg_le_absQ a; have := neg_le_absQ b
  exact absQ_le (by grind) (by grind)

theorem absQ_mul_nonneg (a : Rat) {c : Rat} (hc : 0 ≤ c) : absQ (a * c) = absQ a * c := by
  unfold absQ
  by_cases ha : a < 0
  · have : a * c ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt ha) hc
      grind
    by_cases hac : a * c < 0
    · simp only [ha, hac, ↓reduceIte]; grind
    · simp only [ha, hac, ↓reduceIte]; grind
  · have : 0 ≤ a * c := Rat.mul_nonneg (Rat.not_lt.1 ha) hc
    have hac : ¬ a * c < 0 := Rat.not_lt.2 this
    simp only [ha, hac, ↓reduceIte]

theorem absQ_sum_le {α : Type} (f : α → Rat) :
    ∀ l : List α, absQ (l.map f).sum ≤ (l.map fun a => absQ (f a)).sum
  | [] => by simp only [List.map_nil, List.sum_nil]; unfold absQ; decide
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    have := absQ_add_le (f a) (l.map f).sum
    have := absQ_sum_le f l
    grind

/-! ## 和 -/

theorem sum_map_sub {α : Type} (f g : α → Rat) :
    ∀ l : List α, (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum
  | [] => by simp only [List.map_nil, List.sum_nil]; grind
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_sub f g l]
    grind

theorem sum_le_sum {α : Type} {f g : α → Rat} :
    ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Rat.le_refl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h a (List.mem_cons_self ..)
    have := sum_le_sum (l := l) fun b hb => h b (List.mem_cons_of_mem a hb)
    grind

theorem sum_map_mul_right {α : Type} (f : α → Rat) (c : Rat) (l : List α) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  rw [sum_map_congr (g := fun a => c * f a) (fun a _ => Rat.mul_comm _ _), sum_map_mul_left,
    Rat.mul_comm]

/-- `Σ_a [c = a] · f(a) = f(c)`（重複のないリストで `c` を含むとき）。 -/
theorem sum_indicator_mul {α : Type} [DecidableEq α] (f : α → Rat) (c : α) {l : List α}
    (hnd : l.Nodup) (hc : c ∈ l) :
    (l.map fun a => (if c = a then 1 else 0) * f a).sum = f c := by
  rw [sum_map_congr (g := fun a => if a = c then f c else 0) (fun a _ => by
    by_cases h : a = c
    · subst h; simp only [↓reduceIte]; grind
    · have h' : ¬ c = a := fun e => h e.symm
      simp only [h, h', ↓reduceIte]; grind)]
  exact sum_ite_eq _ _ hnd hc

/-! ## 遷移行列の冪 -/

variable {n : Nat}

theorem pow_nonneg_of {P : Config n → Config n → Rat} (hP : ∀ σ τ, 0 ≤ P σ τ) :
    ∀ (m : Nat) (σ τ : Config n), 0 ≤ pow P m σ τ
  | 0, σ, τ => by
    unfold pow; split
    · decide
    · decide
  | m + 1, σ, τ => by
    unfold pow
    exact sum_nonneg fun a ha => by
      obtain ⟨ρ, _, rfl⟩ := List.mem_map.1 ha
      exact Rat.mul_nonneg (hP σ ρ) (pow_nonneg_of hP m ρ τ)

theorem pow_row_sum {P : Config n → Config n → Rat}
    (hrow : ∀ σ, ((allConfigs n).map fun τ => P σ τ).sum = 1) :
    ∀ (m : Nat) (σ : Config n), ((allConfigs n).map fun τ => pow P m σ τ).sum = 1
  | 0, σ => by
    simp only [pow]
    rw [sum_map_congr (g := fun τ => if τ = σ then (1 : Rat) else 0)
      (fun τ _ => by simp only [eq_comm])]
    exact sum_ite_eq _ _ (nodup_allConfigs n) (mem_allConfigs σ)
  | m + 1, σ => by
    simp only [pow]
    rw [sum_comm, sum_map_congr (g := fun ρ => P σ ρ * 1) (fun ρ _ => by
      rw [sum_map_mul_left, pow_row_sum hrow m ρ])]
    rw [sum_map_congr (g := fun ρ => P σ ρ) (fun ρ _ => Rat.mul_one _)]
    exact hrow σ

/-- Chapman–Kolmogorov：`P^(a+b)(σ → τ) = Σ_ρ P^a(σ → ρ) P^b(ρ → τ)`。 -/
theorem pow_add_apply (P : Config n → Config n → Rat) :
    ∀ (a b : Nat) (σ τ : Config n),
      pow P (a + b) σ τ = ((allConfigs n).map fun ρ => pow P a σ ρ * pow P b ρ τ).sum
  | 0, b, σ, τ => by
    rw [Nat.zero_add]
    exact (sum_indicator_mul (fun ρ => pow P b ρ τ) σ (nodup_allConfigs n) (mem_allConfigs σ)).symm
  | a + 1, b, σ, τ => by
    rw [Nat.add_right_comm]
    show ((allConfigs n).map fun ρ' => P σ ρ' * pow P (a + b) ρ' τ).sum = _
    rw [sum_map_congr (fun ρ' _ => by rw [pow_add_apply P a b ρ' τ, ← sum_map_mul_left])]
    rw [sum_comm]
    apply sum_map_congr
    intro ρ _
    show _ = ((allConfigs n).map fun ρ' => P σ ρ' * pow P a ρ' ρ).sum * pow P b ρ τ
    rw [← sum_map_mul_right]
    exact sum_map_congr fun ρ' _ => (Rat.mul_assoc _ _ _).symm

theorem evolve_zero (P : Config n → Config n → Rat) (μ : Config n → Rat) (τ : Config n) :
    evolve P μ 0 τ = μ τ := by
  unfold evolve
  simp only [pow]
  rw [sum_map_congr (g := fun σ => if σ = τ then μ τ else 0) (fun σ _ => by
    by_cases h : σ = τ
    · subst h; simp only [↓reduceIte]; grind
    · simp only [h, ↓reduceIte]; grind)]
  exact sum_ite_eq _ _ (nodup_allConfigs n) (mem_allConfigs τ)

/-- `μP^(a+b) = (μP^a) P^b`。 -/
theorem evolve_add (P : Config n → Config n → Rat) (μ : Config n → Rat) (a b : Nat) (τ : Config n) :
    evolve P μ (a + b) τ = ((allConfigs n).map fun ρ => evolve P μ a ρ * pow P b ρ τ).sum := by
  unfold evolve
  rw [sum_map_congr (fun σ _ => by rw [pow_add_apply, ← sum_map_mul_left]), sum_comm]
  apply sum_map_congr
  intro ρ _
  rw [← sum_map_mul_right]
  exact sum_map_congr fun σ _ => (Rat.mul_assoc _ _ _).symm

theorem evolve_sum {P : Config n → Config n → Rat}
    (hrow : ∀ σ, ((allConfigs n).map fun τ => P σ τ).sum = 1) (μ : Config n → Rat) (t : Nat) :
    ((allConfigs n).map fun τ => evolve P μ t τ).sum = ((allConfigs n).map μ).sum := by
  unfold evolve
  rw [sum_comm]
  apply sum_map_congr
  intro σ _
  rw [sum_map_mul_left, pow_row_sum hrow t σ, Rat.mul_one]

/-- 定常分布は何ステップたっても変わらない。 -/
theorem evolve_stationary {P : Config n → Config n → Rat} {π : Config n → Rat}
    (hst : Stationary π P) : ∀ (t : Nat) (τ : Config n), evolve P π t τ = π τ
  | 0, τ => evolve_zero P π τ
  | t + 1, τ => by
    rw [Nat.add_comm, evolve_add]
    rw [sum_map_congr (g := fun ρ => π ρ * pow P t ρ τ) (fun ρ _ => by
      rw [show evolve P π 1 ρ = π ρ by
        unfold evolve
        rw [sum_map_congr (g := fun σ => π σ * P σ ρ) (fun σ _ => by
          show π σ * ((allConfigs n).map fun ρ' => P σ ρ' * pow P 0 ρ' ρ).sum = π σ * P σ ρ
          rw [sum_map_congr (g := fun ρ' => (if ρ' = ρ then P σ ρ else 0)) (fun ρ' _ => by
            simp only [pow]
            by_cases h : ρ' = ρ
            · subst h; simp only [↓reduceIte]; grind
            · simp only [h, ↓reduceIte]; grind)]
          rw [sum_ite_eq _ _ (nodup_allConfigs n) (mem_allConfigs ρ)])]
        exact hst ρ])]
    exact evolve_stationary hst t τ

/-! ## L¹ 距離の縮小 -/

/-- **Doeblin の縮小**：`Q` が確率行列で全成分が `δ` 以上なら、和が 0 のベクトル `v` について
`Σ_τ |(vQ)(τ)| ≤ (1 - Nδ) Σ_σ |v(σ)|`。 -/
theorem l1_contract (Q : Config n → Config n → Rat) (δ : Rat) (hQ : ∀ σ τ, δ ≤ Q σ τ)
    (hrow : ∀ σ, ((allConfigs n).map fun τ => Q σ τ).sum = 1)
    (v : Config n → Rat) (hv : ((allConfigs n).map v).sum = 0) :
    ((allConfigs n).map fun τ => absQ ((allConfigs n).map fun σ => v σ * Q σ τ).sum).sum ≤
      (1 - ((allConfigs n).length : Rat) * δ) * ((allConfigs n).map fun σ => absQ (v σ)).sum := by
  -- (vQ)(τ) = Σ_σ v(σ) (Q(σ, τ) - δ)
  have hshift : ∀ τ, ((allConfigs n).map fun σ => v σ * Q σ τ).sum =
      ((allConfigs n).map fun σ => v σ * (Q σ τ - δ)).sum := by
    intro τ
    symm
    rw [sum_map_congr (g := fun σ => v σ * Q σ τ - v σ * δ) (fun σ _ => by grind),
      sum_map_sub, sum_map_mul_right, hv]
    grind
  -- 各 τ で三角不等式
  have hτ : ∀ τ, absQ ((allConfigs n).map fun σ => v σ * Q σ τ).sum ≤
      ((allConfigs n).map fun σ => absQ (v σ) * (Q σ τ - δ)).sum := by
    intro τ
    rw [hshift τ]
    refine Rat.le_trans (absQ_sum_le _ _) (rat_le_of_eq ?_)
    exact sum_map_congr fun σ _ => absQ_mul_nonneg _ (by have := hQ σ τ; grind)
  refine Rat.le_trans (sum_le_sum fun τ _ => hτ τ) (rat_le_of_eq ?_)
  rw [sum_comm]
  rw [sum_map_congr (g := fun σ => absQ (v σ) * (1 - ((allConfigs n).length : Rat) * δ))
    (fun σ _ => by
      rw [sum_map_mul_left, sum_map_sub, hrow σ, sum_map_const])]
  rw [sum_map_mul_right, Rat.mul_comm]

/-! ## 幾何収束 -/

/-- 正の値をとる有限個の条件には、共通の正の下界がある。 -/
theorem exists_common_pos {α : Type} (p : α → Rat → Prop)
    (hmono : ∀ a δ δ', p a δ → δ' ≤ δ → p a δ') :
    ∀ l : List α, (∀ a ∈ l, ∃ δ, 0 < δ ∧ p a δ) → ∃ δ, 0 < δ ∧ ∀ a ∈ l, p a δ
  | [], _ => ⟨1, by decide, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, h => by
    obtain ⟨δa, hδa, ha⟩ := h a (List.mem_cons_self ..)
    obtain ⟨δl, hδl, hl⟩ := exists_common_pos p hmono l fun b hb => h b (List.mem_cons_of_mem a hb)
    refine ⟨min δa δl, by rw [Rat.min_def]; split <;> grind, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hmono b δa _ ha (by rw [Rat.min_def]; split <;> grind)
    · exact hmono b δl _ (hl b hb) (by rw [Rat.min_def]; split <;> grind)

theorem length_allConfigs_pos (n : Nat) : 0 < (allConfigs n).length :=
  List.length_pos_of_mem (mem_allConfigs (allUp n))

/-- **幾何収束（一般の有限マルコフ連鎖）**：`P` が確率行列、`π` が定常な確率分布で、
ある `m > 0` について `P^m` の全成分が正なら、任意の初期分布から `π` へ幾何的に収束する。 -/
theorem geometric_of_primitive {P : Config n → Config n → Rat} {π : Config n → Rat}
    (hP : Stochastic P) (hπ : IsDistribution π) (hst : Stationary π P)
    {m : Nat} (hm : 0 < m) (hpos : ∀ σ τ, 0 < pow P m σ τ) : GeometricConvergence π P := by
  obtain ⟨hP0, hrow⟩ := hP
  let L := allConfigs n
  -- P^m の全成分の正の下界 δ
  obtain ⟨δ, hδ, hδle⟩ := exists_common_pos (fun σ δ => ∀ τ ∈ L, δ ≤ pow P m σ τ)
    (fun _ _ _ h h' τ hτ => Rat.le_trans h' (h τ hτ)) L fun σ _ =>
      exists_common_pos (fun τ δ => δ ≤ pow P m σ τ) (fun _ _ _ h h' => Rat.le_trans h' h) L
        fun τ _ => ⟨pow P m σ τ, hpos σ τ, Rat.le_refl⟩
  have hδ' : ∀ σ τ, δ ≤ pow P m σ τ := fun σ τ => hδle σ (mem_allConfigs σ) τ (mem_allConfigs τ)
  let N : Rat := (L.length : Rat)
  have hN : (1 : Rat) ≤ N := by
    have := length_allConfigs_pos n
    exact Rat.natCast_le_natCast.2 this
  -- N δ ≤ 1（行和が 1 で各成分が δ 以上だから）
  have hNδ : N * δ ≤ 1 := by
    have hs := sum_le_sum (l := L) (f := fun _ => δ) (g := fun τ => pow P m (allUp n) τ)
      fun τ _ => hδ' (allUp n) τ
    rw [sum_map_const, pow_row_sum hrow m (allUp n)] at hs
    exact hs
  refine ⟨m, hm, 1 - N * δ, by grind, ?_, ?_⟩
  · have : 0 < N * δ := by
      have := Rat.mul_le_mul_of_nonneg_right hN (Rat.le_of_lt hδ)
      grind
    grind
  intro μ hμ t
  -- v_t = μP^t - π
  let v : Nat → Config n → Rat := fun t τ => evolve P μ t τ - π τ
  have hv0 : ∀ t, (L.map (v t)).sum = 0 := by
    intro t
    show (L.map fun τ => evolve P μ t τ - π τ).sum = 0
    rw [sum_map_sub, evolve_sum hrow, hμ.2, hπ.2]
    grind
  -- v_{t+s} = v_t P^s
  have hvstep : ∀ t s τ, v (t + s) τ = (L.map fun ρ => v t ρ * pow P s ρ τ).sum := by
    intro t s τ
    show evolve P μ (t + s) τ - π τ = _
    rw [evolve_add, ← evolve_stationary hst s τ]
    unfold evolve
    rw [← sum_map_sub]
    exact sum_map_congr fun ρ _ => by
      show evolve P μ t ρ * pow P s ρ τ - π ρ * pow P s ρ τ = (evolve P μ t ρ - π ρ) * pow P s ρ τ
      grind
  let d : Nat → Rat := fun t => (L.map fun τ => absQ (v t τ)).sum
  have hd : ∀ t, l1Dist (evolve P μ t) π = d t := fun _ => rfl
  -- 1 ステップでは増えない、m ステップで 1 - Nδ 倍以下に縮む
  have hd1 : ∀ t, d (t + 1) ≤ d t := by
    intro t
    have := l1_contract (pow P 1) 0 (pow_nonneg_of hP0 1) (pow_row_sum hrow 1) (v t) (hv0 t)
    have e : d (t + 1) = (L.map fun τ => absQ (L.map fun σ => v t σ * pow P 1 σ τ).sum).sum :=
      sum_map_congr fun τ _ => by rw [hvstep t 1 τ]
    rw [e]; grind
  have hdm : ∀ t, d (t + m) ≤ (1 - N * δ) * d t := by
    intro t
    have := l1_contract (pow P m) δ hδ' (pow_row_sum hrow m) (v t) (hv0 t)
    have e : d (t + m) = (L.map fun τ => absQ (L.map fun σ => v t σ * pow P m σ τ).sum).sum :=
      sum_map_congr fun τ _ => by rw [hvstep t m τ]
    rw [e]; exact this
  -- 初期の距離は 2 以下
  have hd0 : d 0 ≤ 2 := by
    have e : d 0 = (L.map fun τ => absQ (μ τ - π τ)).sum :=
      sum_map_congr fun τ _ => by show absQ (evolve P μ 0 τ - π τ) = _; rw [evolve_zero]
    rw [e]
    have := sum_le_sum (l := L) (f := fun τ => absQ (μ τ - π τ)) (g := fun τ => μ τ + π τ)
      fun τ _ => absQ_le (by have := hπ.1 τ; grind) (by have := hμ.1 τ; grind)
    rw [sum_map_add, hμ.2, hπ.2] at this
    grind
  have hdle2 : ∀ t, d t ≤ 2 := by
    intro t
    induction t with
    | zero => exact hd0
    | succ t ih => exact Rat.le_trans (hd1 t) ih
  have hρ0 : 0 ≤ 1 - N * δ := by grind
  -- d (k m + r) ≤ 2 ρ^k
  have hdk : ∀ k r, d (m * k + r) ≤ 2 * (1 - N * δ) ^ k := by
    intro k
    induction k with
    | zero => intro r; simp only [Nat.mul_zero, Nat.zero_add, Rat.pow_zero]; grind [hdle2 r]
    | succ k ih =>
      intro r
      have e : m * (k + 1) + r = (m * k + r) + m := by rw [Nat.mul_succ]; omega
      rw [e, Rat.pow_succ]
      have h1 := hdm (m * k + r)
      have h2 := Rat.mul_le_mul_of_nonneg_left (ih r) hρ0
      grind
  rw [hd]
  have := hdk (t / m) (t % m)
  rwa [Nat.div_add_mod] at this

/-! ## `ρ^k → 0` -/

theorem exists_nat_gt (q : Rat) : ∃ k : Nat, q < k := by
  refine ⟨q.floor.toNat + 1, ?_⟩
  have h1 := Rat.lt_floor_add_one q
  have h2 : q.floor + 1 ≤ ((q.floor.toNat + 1 : Nat) : Int) := by
    have := Int.self_le_toNat q.floor
    omega
  have h3 : ((q.floor + 1 : Int) : Rat) ≤ (((q.floor.toNat + 1 : Nat) : Int) : Rat) :=
    Rat.intCast_le_intCast.2 h2
  rw [Rat.intCast_natCast] at h3
  grind

/-- Bernoulli の不等式：`0 ≤ ρ ≤ 1` なら `ρ^k (1 + k(1 - ρ)) ≤ 1`。 -/
theorem bernoulli {ρ : Rat} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    ∀ k : Nat, ρ ^ k * (1 + (k : Rat) * (1 - ρ)) ≤ 1
  | 0 => by simp only [Rat.pow_zero]; grind
  | k + 1 => by
    have ih := bernoulli h0 h1 k
    have hpk : 0 ≤ ρ ^ k := Rat.pow_nonneg h0
    have hsq : 0 ≤ ((k : Rat) + 1) * ((1 - ρ) * (1 - ρ)) :=
      Rat.mul_nonneg (by have := (Rat.natCast_nonneg (a := k)); grind)
        (Rat.mul_nonneg (by grind) (by grind))
    have hstep : ρ * (1 + ((k : Rat) + 1) * (1 - ρ)) ≤ 1 + (k : Rat) * (1 - ρ) := by grind
    have := Rat.mul_le_mul_of_nonneg_left hstep hpk
    rw [Rat.pow_succ]
    have e : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by push_cast; rfl
    rw [e]
    grind

theorem exists_pow_lt {ρ ε : Rat} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hε : 0 < ε) : ∃ k : Nat, ρ ^ k < ε := by
  have ha : 0 < 1 - ρ := by grind
  have hae : 0 < (1 - ρ) * ε := by
    have := Rat.mul_lt_mul_of_pos_right ha hε
    grind
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ((1 - ρ) * ε))
  refine ⟨k, Rat.not_le.1 fun hle => ?_⟩
  have hb := bernoulli h0 (Rat.le_of_lt h1) k
  have hk' : 1 < (k : Rat) * ((1 - ρ) * ε) := by
    have := (Rat.div_lt_iff hae).1 hk
    grind
  have hpos : 0 ≤ 1 + (k : Rat) * (1 - ρ) :=
    by have := Rat.mul_nonneg (Rat.natCast_nonneg (a := k)) (Rat.le_of_lt ha); grind
  have := Rat.mul_le_mul_of_nonneg_right hle hpos
  grind

theorem pow_antitone {ρ : Rat} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {a b : Nat} (h : a ≤ b) : ρ ^ b ≤ ρ ^ a := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add']
  have := pow_le_one' h0 h1 c
  have := Rat.mul_le_mul_of_nonneg_left this (Rat.pow_nonneg (n := a) h0)
  grind

theorem absQ_le_l1 (μ ν : Config n → Rat) (τ : Config n) : absQ (μ τ - ν τ) ≤ l1Dist μ ν :=
  le_sum_of_mem (fun _ hb => by
      obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hb
      exact absQ_nonneg _)
    (List.mem_map_of_mem (mem_allConfigs τ))

/-- 幾何収束なら収束する。 -/
theorem converges_of_geometric {P : Config n → Config n → Rat} {π : Config n → Rat}
    (h : GeometricConvergence π P) : Converges π P := by
  obtain ⟨m, hm, ρ, hρ0, hρ1, hbound⟩ := h
  intro μ hμ ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt hρ0 hρ1 (show 0 < ε / 2 by grind)
  refine ⟨k * m, fun t ht τ => ?_⟩
  have hkt : k ≤ t / m := (Nat.le_div_iff_mul_le hm).2 ht
  have h1 := hbound μ hμ t
  have h2 := pow_antitone hρ0 (Rat.le_of_lt hρ1) hkt
  have h3 := absQ_le_l1 (evolve P μ t) π τ
  have h4 := le_absQ (evolve P μ t τ - π τ)
  have h5 := neg_le_absQ (evolve P μ t τ - π τ)
  constructor <;> grind

/-! ## Metropolis 核への適用 -/

variable {G : Graph} {x : Rat}

theorem partition_pos (hx : 0 < x) : 0 < partition G x :=
  sum_pos_of_mem (fun _ hb => by
      obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hb
      exact Rat.le_of_lt (weight_pos hx σ))
    (List.mem_map_of_mem (mem_allConfigs (allUp G.n))) (weight_pos hx _)

/-- Boltzmann 分布は確率分布。 -/
theorem boltzmann_isDistribution (G : Graph) (x : Rat) (hx : 0 < x) :
    IsDistribution (boltzmann G x) := by
  have hZ := partition_pos (G := G) hx
  refine ⟨fun σ => ?_, ?_⟩
  · unfold boltzmann
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt (weight_pos hx σ)) (Rat.le_of_lt (Rat.inv_pos.2 hZ))
  · unfold boltzmann
    simp only [Rat.div_def]
    rw [sum_map_mul_right]
    exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hZ)

theorem n_pos_of_bond (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) : 0 < G.n := by
  obtain ⟨⟨u, _⟩, _, _⟩ := hG
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt

/-- **幾何収束**：`0 < x < 1` で自己ループでないボンドがあれば、Metropolis 連鎖は任意の初期分布から
Boltzmann 分布へ幾何的に収束する（`m = 2n` ステップごとに L¹ 距離が一定の比 `ρ < 1` 以下に縮む）。 -/
theorem metropolis_geometric (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    GeometricConvergence (boltzmann G x) (kernel G x) := by
  have hn := n_pos_of_bond hG
  exact geometric_of_primitive (stochastic G x hx0 hn) (boltzmann_isDistribution G x hx0)
    (stationary G x hx0 hn) (m := 2 * G.n) (by omega)
    (ergodic_from G x hx0 hx1 hG (2 * G.n) (Nat.le_refl _))

/-- **収束**：Metropolis 連鎖は任意の初期分布から Boltzmann 分布へ収束する。 -/
theorem metropolis_converges (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    Converges (boltzmann G x) (kernel G x) :=
  converges_of_geometric (metropolis_geometric G x hx0 hx1 hG)

end LeanIsing.Proofs
