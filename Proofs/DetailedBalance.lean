import Proofs.Lemmas

/-!
# 詳細釣り合いと定常性

任意の相互作用グラフ `G` と任意の `x > 0` について、仕様の Metropolis 核 `kernel G x` が
Boltzmann 分布 `π(σ) = x ^ unsat σ / Z` に関して詳細釣り合いを満たすことを証明する。

証明の要点は、サイト `i` を選んだ場合の寄与ごとに

  `w(σ) · [flip σ i = τ] · min(1, w(τ)/w(σ)) = [flip σ i = τ] · min(w(σ), w(τ))`

が `σ` と `τ` について対称になること（`flip σ i = τ ↔ flip τ i = σ`）。
さらに、各行の和が 1 であること（確率核であること）と合わせて定常性 `πP = π` を導く。
-/

namespace LeanIsing.Proofs

variable {G : Graph} {x : Rat}

theorem weight_pos (hx : 0 < x) (σ : Config G.n) : 0 < weight G x σ := Rat.pow_pos hx

/-- `w(σ) · min(1, w(σ')/w(σ)) = min(w(σ), w(σ'))`。 -/
theorem weight_mul_accept (hx : 0 < x) (σ : Config G.n) (i : Fin G.n) :
    weight G x σ * accept G x σ i = min (weight G x σ) (weight G x (flip σ i)) :=
  mul_min_div (weight_pos hx σ)

theorem accept_pos (hx : 0 < x) (σ : Config G.n) (i : Fin G.n) : 0 < accept G x σ i := by
  unfold accept
  have h1 := weight_pos hx (flip σ i)
  have h2 := weight_pos hx σ
  have : 0 < weight G x (flip σ i) / weight G x σ := (Rat.lt_div_iff h2).2 (by grind)
  rw [Rat.min_def]; split <;> grind

theorem accept_le_one (σ : Config G.n) (i : Fin G.n) : accept G x σ i ≤ 1 := by
  unfold accept
  rw [Rat.min_def]; split <;> grind

/-- 遷移確率のうち、サイト `i` を選んだ場合の寄与（`1/n` 倍する前）。 -/
def term (G : Graph) (x : Rat) (σ τ : Config G.n) (i : Fin G.n) : Rat :=
  (if flip σ i = τ then accept G x σ i else 0) + (if σ = τ then 1 - accept G x σ i else 0)

theorem kernel_eq (σ τ : Config G.n) :
    kernel G x σ τ = ((List.finRange G.n).map (term G x σ τ)).sum / G.n := rfl

theorem term_nonneg (hx : 0 < x) (σ τ : Config G.n) (i : Fin G.n) : 0 ≤ term G x σ τ i := by
  have h0 := accept_pos hx σ i
  have h1 := accept_le_one (x := x) σ i
  unfold term
  split <;> split <;> grind

/-- サイトごとの対称性：`w(σ) · term(σ, τ, i) = w(τ) · term(τ, σ, i)`。 -/
theorem weight_mul_term (hx : 0 < x) (σ τ : Config G.n) (i : Fin G.n) :
    weight G x σ * term G x σ τ i = weight G x τ * term G x τ σ i := by
  by_cases hστ : σ = τ
  · subst hστ; rfl
  · have hτσ : τ ≠ σ := Ne.symm hστ
    unfold term
    simp only [hστ, hτσ, ↓reduceIte]
    by_cases hf : flip σ i = τ
    · have hf' : flip τ i = σ := flip_eq_comm.1 hf
      simp only [hf, hf', ↓reduceIte]
      have e1 := weight_mul_accept hx σ i
      have e2 := weight_mul_accept hx τ i
      rw [hf] at e1
      rw [hf'] at e2
      rw [Rat.min_def] at e1 e2
      split at e1 <;> split at e2 <;> grind
    · have hf' : ¬ flip τ i = σ := fun h => hf (flip_eq_comm.2 h)
      simp only [hf, hf', ↓reduceIte]
      grind

/-- 規格化前の重みに関する詳細釣り合い。 -/
theorem weight_detailed_balance (hx : 0 < x) (σ τ : Config G.n) :
    weight G x σ * kernel G x σ τ = weight G x τ * kernel G x τ σ := by
  rw [kernel_eq, kernel_eq, Rat.div_def, Rat.div_def, ← Rat.mul_assoc, ← Rat.mul_assoc,
    ← sum_map_mul_left, ← sum_map_mul_left,
    sum_map_congr (fun i _ => weight_mul_term hx σ τ i)]

/-- **詳細釣り合い**：任意のグラフと任意の `x > 0` について `π(σ) P(σ → τ) = π(τ) P(τ → σ)`。 -/
theorem detailed_balance (G : Graph) (x : Rat) (hx : 0 < x) :
    Chain.DetailedBalance (boltzmann G x) (kernel G x) := by
  intro σ τ
  unfold boltzmann
  have := weight_detailed_balance hx σ τ
  rw [Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_comm (partition G x)⁻¹, ← Rat.mul_assoc, this,
    Rat.mul_assoc, Rat.mul_comm (kernel G x τ σ), ← Rat.mul_assoc]

/-! ## 確率核であること（各行の和が 1）と定常性 -/

theorem sum_map_const {α : Type} (c : Rat) : ∀ l : List α, (l.map fun _ => c).sum = l.length * c
  | [] => by simp only [List.map_nil, List.sum_nil, List.length_nil]; grind
  | _ :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_const c l, List.length_cons]
    rw [Rat.natCast_add]; grind

theorem kernel_nonneg (hx : 0 < x) (σ τ : Config G.n) : 0 ≤ kernel G x σ τ := by
  rw [kernel_eq]
  have hs : 0 ≤ ((List.finRange G.n).map (term G x σ τ)).sum :=
    sum_nonneg fun a ha => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
      exact term_nonneg hx σ τ i
  have hn : (0 : Rat) ≤ G.n := Rat.natCast_nonneg
  rw [Rat.div_def]
  have : 0 ≤ (G.n : Rat)⁻¹ := by
    rcases Nat.eq_zero_or_pos G.n with h | h
    · rw [h]; simp
    · exact Rat.le_of_lt (Rat.inv_pos.2 (Rat.natCast_pos.2 h))
  exact Rat.mul_nonneg hs this

/-- 各サイトの寄与を、行き先 `τ` について全配位で足すと 1。 -/
theorem sum_term (σ : Config G.n) (i : Fin G.n) :
    ((allConfigs G.n).map fun τ => term G x σ τ i).sum = 1 := by
  unfold term
  rw [sum_map_add]
  have e1 : ((allConfigs G.n).map fun τ => if flip σ i = τ then accept G x σ i else 0).sum =
      accept G x σ i := by
    rw [sum_map_congr (g := fun τ => if τ = flip σ i then accept G x σ i else 0)
        (fun τ _ => by simp only [eq_comm])]
    exact sum_ite_eq _ _ (nodup_allConfigs _) (mem_allConfigs _)
  have e2 : ((allConfigs G.n).map fun τ => if σ = τ then 1 - accept G x σ i else 0).sum =
      1 - accept G x σ i := by
    rw [sum_map_congr (g := fun τ => if τ = σ then 1 - accept G x σ i else 0)
        (fun τ _ => by simp only [eq_comm])]
    exact sum_ite_eq _ _ (nodup_allConfigs _) (mem_allConfigs _)
  rw [e1, e2]
  grind

/-- 遷移確率は確率核：各行の和が 1（サイトが 1 個以上あるとき）。 -/
theorem kernel_row_sum (hn : 0 < G.n) (σ : Config G.n) :
    ((allConfigs G.n).map fun τ => kernel G x σ τ).sum = 1 := by
  simp only [kernel_eq, Rat.div_def]
  rw [sum_map_congr (g := fun τ => (G.n : Rat)⁻¹ * ((List.finRange G.n).map (term G x σ τ)).sum)
      (fun τ _ => Rat.mul_comm _ _),
    sum_map_mul_left, sum_comm, sum_map_congr (fun i _ => sum_term σ i), sum_map_const,
    List.length_finRange, Rat.mul_one, Rat.mul_comm]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.2 hn))

/-- **確率行列**：Metropolis 核は成分が非負で各行の和が 1（サイトが 1 個以上あるとき）。 -/
theorem stochastic (G : Graph) (x : Rat) (hx : 0 < x) (hn : 0 < G.n) :
    Chain.Stochastic (kernel G x) :=
  ⟨kernel_nonneg hx, kernel_row_sum hn⟩

/-- **定常性**：Boltzmann 分布は Metropolis 核の定常分布である（`πP = π`）。
詳細釣り合いと、各行の和が 1 であることから従う。 -/
theorem stationary (G : Graph) (x : Rat) (hx : 0 < x) (hn : 0 < G.n) :
    Chain.Stationary (boltzmann G x) (kernel G x) := by
  intro τ
  rw [sum_map_congr (g := fun σ => boltzmann G x τ * kernel G x τ σ)
      (fun σ _ => detailed_balance G x hx σ τ),
    sum_map_mul_left, kernel_row_sum hn, Rat.mul_one]

end LeanIsing.Proofs
