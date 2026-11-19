import Proofs.Lemmas

/-!
# 詳細釣り合いと定常性

任意の正の重み `w` について、Metropolis 核 `metropolis w` が分布 `normalize w = w / Σ w` に関して
詳細釣り合いを満たすことを証明する（`general_detailed_balance`）。
古典 Ising 模型（`kernel G x = metropolis (weight G x)`）はその特別な場合である。

証明の要点は、サイト `i` を選んだ場合の寄与ごとに

  `w(σ) · [flip σ i = τ] · min(1, w(τ)/w(σ)) = [flip σ i = τ] · min(w(σ), w(τ))`

が `σ` と `τ` について対称になること（`flip σ i = τ ↔ flip τ i = σ`）。
さらに、各行の和が 1 であること（確率核であること）と合わせて定常性 `πP = π` を導く。
-/

namespace LeanIsing.Proofs

/-! ## 一般の重み -/

section General

variable {n : Nat} {w : Config n → Rat}

/-- `w(σ) · min(1, w(σ')/w(σ)) = min(w(σ), w(σ'))`。 -/
theorem mul_acceptW (hw : ∀ σ, 0 < w σ) (σ : Config n) (i : Fin n) :
    w σ * acceptW w σ i = min (w σ) (w (flip σ i)) :=
  mul_min_div (hw σ)

theorem acceptW_pos (hw : ∀ σ, 0 < w σ) (σ : Config n) (i : Fin n) : 0 < acceptW w σ i := by
  unfold acceptW
  have h1 := hw (flip σ i)
  have h2 := hw σ
  have : 0 < w (flip σ i) / w σ := (Rat.lt_div_iff h2).2 (by grind)
  rw [Rat.min_def]; split <;> grind

theorem acceptW_le_one (σ : Config n) (i : Fin n) : acceptW w σ i ≤ 1 := by
  unfold acceptW
  rw [Rat.min_def]; split <;> grind

/-- 遷移確率のうち、サイト `i` を選んだ場合の寄与（`1/n` 倍する前）。 -/
def term (w : Config n → Rat) (σ τ : Config n) (i : Fin n) : Rat :=
  (if flip σ i = τ then acceptW w σ i else 0) + (if σ = τ then 1 - acceptW w σ i else 0)

theorem metropolis_eq (σ τ : Config n) :
    metropolis w σ τ = ((List.finRange n).map (term w σ τ)).sum / n := rfl

theorem term_nonneg (hw : ∀ σ, 0 < w σ) (σ τ : Config n) (i : Fin n) : 0 ≤ term w σ τ i := by
  have h0 := acceptW_pos hw σ i
  have h1 := acceptW_le_one (w := w) σ i
  unfold term
  split <;> split <;> grind

/-- サイトごとの対称性：`w(σ) · term(σ, τ, i) = w(τ) · term(τ, σ, i)`。 -/
theorem mul_term (hw : ∀ σ, 0 < w σ) (σ τ : Config n) (i : Fin n) :
    w σ * term w σ τ i = w τ * term w τ σ i := by
  by_cases hστ : σ = τ
  · subst hστ; rfl
  · have hτσ : τ ≠ σ := Ne.symm hστ
    unfold term
    simp only [hστ, hτσ, ↓reduceIte]
    by_cases hf : flip σ i = τ
    · have hf' : flip τ i = σ := flip_eq_comm.1 hf
      simp only [hf, hf', ↓reduceIte]
      have e1 := mul_acceptW hw σ i
      have e2 := mul_acceptW hw τ i
      rw [hf] at e1
      rw [hf'] at e2
      rw [Rat.min_def] at e1 e2
      split at e1 <;> split at e2 <;> grind
    · have hf' : ¬ flip τ i = σ := fun h => hf (flip_eq_comm.2 h)
      simp only [hf, hf', ↓reduceIte]
      grind

/-- 規格化前の重みに関する詳細釣り合い。 -/
theorem weight_detailed_balance' (hw : ∀ σ, 0 < w σ) (σ τ : Config n) :
    w σ * metropolis w σ τ = w τ * metropolis w τ σ := by
  rw [metropolis_eq, metropolis_eq, Rat.div_def, Rat.div_def, ← Rat.mul_assoc, ← Rat.mul_assoc,
    ← sum_map_mul_left, ← sum_map_mul_left,
    sum_map_congr (fun i _ => mul_term hw σ τ i)]

/-- **詳細釣り合い（一般の重み）**：`π = w / Σ w` について `π(σ) P(σ → τ) = π(τ) P(τ → σ)`。 -/
theorem general_detailed_balance (w : Config n → Rat) (hw : ∀ σ, 0 < w σ) :
    Chain.DetailedBalance (normalize w) (metropolis w) := by
  intro σ τ
  unfold normalize
  have := weight_detailed_balance' hw σ τ
  generalize ((allConfigs n).map w).sum = Z
  rw [Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_comm Z⁻¹, ← Rat.mul_assoc, this,
    Rat.mul_assoc, Rat.mul_comm (metropolis w τ σ), ← Rat.mul_assoc]

theorem sum_map_const {α : Type} (c : Rat) : ∀ l : List α, (l.map fun _ => c).sum = l.length * c
  | [] => by simp only [List.map_nil, List.sum_nil, List.length_nil]; grind
  | _ :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_const c l, List.length_cons]
    rw [Rat.natCast_add]; grind

theorem metropolis_nonneg (hw : ∀ σ, 0 < w σ) (σ τ : Config n) : 0 ≤ metropolis w σ τ := by
  rw [metropolis_eq]
  have hs : 0 ≤ ((List.finRange n).map (term w σ τ)).sum :=
    sum_nonneg fun a ha => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
      exact term_nonneg hw σ τ i
  rw [Rat.div_def]
  have : 0 ≤ (n : Rat)⁻¹ := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · exact Rat.le_of_lt (Rat.inv_pos.2 (Rat.natCast_pos.2 h))
  exact Rat.mul_nonneg hs this

/-- 各サイトの寄与を、行き先 `τ` について全配位で足すと 1。 -/
theorem sum_term (σ : Config n) (i : Fin n) :
    ((allConfigs n).map fun τ => term w σ τ i).sum = 1 := by
  unfold term
  rw [sum_map_add]
  have e1 : ((allConfigs n).map fun τ => if flip σ i = τ then acceptW w σ i else 0).sum =
      acceptW w σ i := by
    rw [sum_map_congr (g := fun τ => if τ = flip σ i then acceptW w σ i else 0)
        (fun τ _ => by simp only [eq_comm])]
    exact sum_ite_eq _ _ (nodup_allConfigs _) (mem_allConfigs _)
  have e2 : ((allConfigs n).map fun τ => if σ = τ then 1 - acceptW w σ i else 0).sum =
      1 - acceptW w σ i := by
    rw [sum_map_congr (g := fun τ => if τ = σ then 1 - acceptW w σ i else 0)
        (fun τ _ => by simp only [eq_comm])]
    exact sum_ite_eq _ _ (nodup_allConfigs _) (mem_allConfigs _)
  rw [e1, e2]
  grind

/-- Metropolis 核は確率核：各行の和が 1（サイトが 1 個以上あるとき）。 -/
theorem metropolis_row_sum (hn : 0 < n) (σ : Config n) :
    ((allConfigs n).map fun τ => metropolis w σ τ).sum = 1 := by
  simp only [metropolis_eq, Rat.div_def]
  rw [sum_map_congr (g := fun τ => (n : Rat)⁻¹ * ((List.finRange n).map (term w σ τ)).sum)
      (fun τ _ => Rat.mul_comm _ _),
    sum_map_mul_left, sum_comm, sum_map_congr (fun i _ => sum_term σ i), sum_map_const,
    List.length_finRange, Rat.mul_one, Rat.mul_comm]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.2 hn))

/-- **確率行列（一般の重み）**。 -/
theorem general_stochastic (w : Config n → Rat) (hw : ∀ σ, 0 < w σ) (hn : 0 < n) :
    Chain.Stochastic (metropolis w) :=
  ⟨metropolis_nonneg hw, metropolis_row_sum hn⟩

/-- **定常性（一般の重み）**：`normalize w` は Metropolis 核の定常分布である。 -/
theorem general_stationary (w : Config n → Rat) (hw : ∀ σ, 0 < w σ) (hn : 0 < n) :
    Chain.Stationary (normalize w) (metropolis w) := by
  intro τ
  rw [sum_map_congr (g := fun σ => normalize w τ * metropolis w τ σ)
      (fun σ _ => general_detailed_balance w hw σ τ),
    sum_map_mul_left, metropolis_row_sum hn, Rat.mul_one]

end General

/-! ## 古典 Ising 模型 -/

variable {G : Graph} {x : Rat}

theorem weight_pos (hx : 0 < x) (σ : Config G.n) : 0 < weight G x σ := Rat.pow_pos hx

theorem accept_pos (hx : 0 < x) (σ : Config G.n) (i : Fin G.n) : 0 < accept G x σ i :=
  acceptW_pos (weight_pos hx) σ i

theorem accept_le_one (σ : Config G.n) (i : Fin G.n) : accept G x σ i ≤ 1 :=
  acceptW_le_one σ i

theorem kernel_eq (σ τ : Config G.n) :
    kernel G x σ τ = ((List.finRange G.n).map (term (weight G x) σ τ)).sum / G.n := rfl

theorem kernel_nonneg (hx : 0 < x) (σ τ : Config G.n) : 0 ≤ kernel G x σ τ :=
  metropolis_nonneg (weight_pos hx) σ τ

theorem kernel_row_sum (hn : 0 < G.n) (σ : Config G.n) :
    ((allConfigs G.n).map fun τ => kernel G x σ τ).sum = 1 :=
  metropolis_row_sum hn σ

/-- **詳細釣り合い**：任意のグラフと任意の `x > 0` について `π(σ) P(σ → τ) = π(τ) P(τ → σ)`。 -/
theorem detailed_balance (G : Graph) (x : Rat) (hx : 0 < x) :
    Chain.DetailedBalance (boltzmann G x) (kernel G x) :=
  general_detailed_balance (weight G x) (weight_pos hx)

/-- **確率行列**：Metropolis 核は成分が非負で各行の和が 1（サイトが 1 個以上あるとき）。 -/
theorem stochastic (G : Graph) (x : Rat) (hx : 0 < x) (hn : 0 < G.n) :
    Chain.Stochastic (kernel G x) :=
  general_stochastic (weight G x) (weight_pos hx) hn

/-- **定常性**：Boltzmann 分布は Metropolis 核の定常分布である（`πP = π`）。 -/
theorem stationary (G : Graph) (x : Rat) (hx : 0 < x) (hn : 0 < G.n) :
    Chain.Stationary (boltzmann G x) (kernel G x) :=
  general_stationary (weight G x) (weight_pos hx) hn

end LeanIsing.Proofs
