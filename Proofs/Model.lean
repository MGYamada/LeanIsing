import Proofs.Convergence

/-!
# 異方的な模型の Metropolis 法

ボンドの層ごとに Boltzmann 因子をもつ模型 `Model` について、一般の重みの定理
（`general_*`）を当てはめる。仮定は次の 2 つだけである。

* `Valid`：すべての因子が `0 < x_l ≤ 1`。重みは正になる。
* `Frustratable`：因子が 1 未満の層に自己ループでないボンド `(u, v)` がある。
  全上向き配位で `u` を反転すると重みが減るので、その場にとどまる確率が正になる（非周期性）。

古典模型は 1 層の模型と一致する（`toModel_kernel`、`toModel_boltzmann`）。
-/

namespace LeanIsing.Proofs

open Chain

variable {n : Nat}

theorem layerWeight_pos (σ : Config n) :
    ∀ ls : List (List (Fin n × Fin n) × Rat), (∀ l ∈ ls, 0 < l.2) → 0 < layerWeight σ ls
  | [], _ => by unfold layerWeight; decide
  | l :: rest, h => by
    unfold layerWeight
    exact Rat.mul_pos (Rat.pow_pos (h l (List.mem_cons_self ..)))
      (layerWeight_pos σ rest fun l' hl' => h l' (List.mem_cons_of_mem l hl'))

theorem layerWeight_nonneg_le_one (σ : Config n) :
    ∀ ls : List (List (Fin n × Fin n) × Rat), (∀ l ∈ ls, 0 < l.2 ∧ l.2 ≤ 1) →
      0 ≤ layerWeight σ ls ∧ layerWeight σ ls ≤ 1
  | [], _ => by unfold layerWeight; decide
  | l :: rest, h => by
    unfold layerWeight
    have hl := h l (List.mem_cons_self ..)
    obtain ⟨h0, h1⟩ := layerWeight_nonneg_le_one σ rest fun l' hl' => h l' (List.mem_cons_of_mem l hl')
    have hp0 : 0 ≤ l.2 ^ unsatOf l.1 σ := Rat.pow_nonneg (Rat.le_of_lt hl.1)
    have hp1 : l.2 ^ unsatOf l.1 σ ≤ 1 := pow_le_one' (Rat.le_of_lt hl.1) hl.2 _
    refine ⟨Rat.mul_nonneg hp0 h0, ?_⟩
    have := Rat.mul_le_mul_of_nonneg_left h1 hp0
    grind

/-- 因子がすべて `(0, 1]` なら、重みはどの層の因子 `x_l ^ unsat_l` 以下。 -/
theorem layerWeight_le_factor (σ : Config n) :
    ∀ ls : List (List (Fin n × Fin n) × Rat), (∀ l ∈ ls, 0 < l.2 ∧ l.2 ≤ 1) →
      ∀ l ∈ ls, layerWeight σ ls ≤ l.2 ^ unsatOf l.1 σ
  | [], _, _, h => absurd h List.not_mem_nil
  | l :: rest, h, l', hl' => by
    unfold layerWeight
    have hl := h l (List.mem_cons_self ..)
    have hrest : ∀ l'' ∈ rest, 0 < l''.2 ∧ l''.2 ≤ 1 := fun l'' h'' => h l'' (List.mem_cons_of_mem l h'')
    have hp0 : 0 ≤ l.2 ^ unsatOf l.1 σ := Rat.pow_nonneg (Rat.le_of_lt hl.1)
    have hp1 : l.2 ^ unsatOf l.1 σ ≤ 1 := pow_le_one' (Rat.le_of_lt hl.1) hl.2 _
    obtain ⟨hr0, hr1⟩ := layerWeight_nonneg_le_one σ rest hrest
    rcases List.mem_cons.1 hl' with rfl | hl'
    · have := Rat.mul_le_mul_of_nonneg_left hr1 hp0
      grind
    · have := layerWeight_le_factor σ rest hrest l' hl'
      have := Rat.mul_le_mul_of_nonneg_right hp1 hr0
      have := Rat.mul_le_mul_of_nonneg_left (layerWeight_le_factor σ rest hrest l' hl') hp0
      grind

theorem unsatOf_allUp (bs : List (Fin n × Fin n)) : unsatOf bs (allUp n) = 0 := by
  unfold unsatOf
  rw [List.countP_eq_zero]
  intro b _
  simp [allUp_get]

theorem layerWeight_allUp : ∀ ls : List (List (Fin n × Fin n) × Rat), layerWeight (allUp n) ls = 1
  | [] => rfl
  | l :: rest => by
    unfold layerWeight
    rw [unsatOf_allUp, Rat.pow_zero, layerWeight_allUp rest, Rat.mul_one]

namespace Model

variable {M : Model}

theorem weight_pos (hM : M.Valid) (σ : Config M.n) : 0 < M.weight σ :=
  layerWeight_pos σ M.layers fun l hl => (hM l hl).1

/-- 反転で重みが減る配位とサイトがある（全上向き配位の、ボンドの端点）。 -/
theorem exists_rejection (hM : M.Valid) (hF : M.Frustratable) :
    ∃ σ₀ i₀, M.weight (flip σ₀ i₀) < M.weight σ₀ := by
  obtain ⟨l, hl, hlt, ⟨u, v⟩, hb, huv⟩ := hF
  refine ⟨allUp M.n, u, ?_⟩
  have h1 := layerWeight_le_factor (flip (allUp M.n) u) M.layers hM l hl
  have hU : 0 < unsatOf l.1 (flip (allUp M.n) u) :=
    unsat_flip_allUp_pos (G := ⟨M.n, l.1⟩) hb huv
  have h2 := pow_lt_one' (Rat.le_of_lt (hM l hl).1) hlt hU
  show layerWeight (flip (allUp M.n) u) M.layers < layerWeight (allUp M.n) M.layers
  rw [layerWeight_allUp]
  grind

theorem n_pos (hF : M.Frustratable) : 0 < M.n := by
  obtain ⟨_, _, _, ⟨u, _⟩, _, _⟩ := hF
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt

end Model

/-! ## 主定理（異方的な模型） -/

theorem model_stochastic (M : Model) (hM : M.Valid) (hn : 0 < M.n) : Stochastic M.kernel :=
  general_stochastic M.weight (Model.weight_pos hM) hn

theorem model_detailed_balance (M : Model) (hM : M.Valid) :
    DetailedBalance M.boltzmann M.kernel :=
  general_detailed_balance M.weight (Model.weight_pos hM)

theorem model_stationary (M : Model) (hM : M.Valid) (hn : 0 < M.n) :
    Stationary M.boltzmann M.kernel :=
  general_stationary M.weight (Model.weight_pos hM) hn

theorem model_irreducible (M : Model) (hM : M.Valid) : Irreducible M.kernel :=
  general_irreducible M.weight (Model.weight_pos hM)

theorem model_ergodic (M : Model) (hM : M.Valid) (hF : M.Frustratable) : Ergodic M.kernel :=
  general_ergodic M.weight (Model.weight_pos hM) (Model.exists_rejection hM hF)

theorem model_geometric (M : Model) (hM : M.Valid) (hF : M.Frustratable) :
    GeometricConvergence M.boltzmann M.kernel :=
  general_geometric M.weight (Model.weight_pos hM) (Model.n_pos hF) (Model.exists_rejection hM hF)

theorem model_converges (M : Model) (hM : M.Valid) (hF : M.Frustratable) :
    Converges M.boltzmann M.kernel :=
  converges_of_geometric (model_geometric M hM hF)

/-! ## 古典模型は 1 層の模型 -/

theorem toModel_weight (G : Graph) (x : Rat) : (G.toModel x).weight = weight G x := by
  funext σ
  show x ^ unsatOf G.bonds σ * 1 = x ^ G.unsat σ
  rw [Rat.mul_one]; rfl

theorem toModel_kernel (G : Graph) (x : Rat) : (G.toModel x).kernel = kernel G x := by
  show metropolis (G.toModel x).weight = metropolis (weight G x)
  rw [toModel_weight]
  rfl

theorem toModel_boltzmann (G : Graph) (x : Rat) : (G.toModel x).boltzmann = boltzmann G x := by
  show normalize (G.toModel x).weight = normalize (weight G x)
  rw [toModel_weight]
  rfl

end LeanIsing.Proofs
