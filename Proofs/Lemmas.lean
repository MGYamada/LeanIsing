import LeanIsing.Spec

/-!
# 基本補題

スピン反転、全配位の列挙、`Rat` のリストの和についての補題。
-/

namespace LeanIsing.Proofs

/-! ## スピン反転 -/

theorem flip_get {n : Nat} (σ : Config n) (i : Fin n) (j : Nat) (hj : j < n) :
    (flip σ i)[j] = if (i : Nat) = j then !σ[(i : Nat)] else σ[j] := by
  unfold flip
  simp only [Fin.getElem_fin, Vector.getElem_set]

@[simp] theorem flip_get_self {n : Nat} (σ : Config n) (i : Fin n) :
    (flip σ i)[(i : Nat)] = !σ[(i : Nat)] := by
  rw [flip_get]; simp

theorem flip_get_ne {n : Nat} (σ : Config n) {i : Fin n} {j : Nat} {hj : j < n} (h : (i : Nat) ≠ j) :
    (flip σ i)[j] = σ[j] := by
  rw [flip_get]; simp [h]

@[simp] theorem flip_flip {n : Nat} (σ : Config n) (i : Fin n) : flip (flip σ i) i = σ := by
  apply Vector.ext
  intro j hj
  by_cases h : (i : Nat) = j
  · subst h; simp
  · rw [flip_get_ne _ h, flip_get_ne _ h]

theorem flip_ne {n : Nat} (σ : Config n) (i : Fin n) : flip σ i ≠ σ := by
  intro h
  have := congrArg (fun τ : Config n => τ[(i : Nat)]) h
  simp only [flip_get_self] at this
  cases hσ : σ[(i : Nat)] <;> simp [hσ] at this

theorem flip_eq_comm {n : Nat} {σ τ : Config n} {i : Fin n} : flip σ i = τ ↔ flip τ i = σ := by
  constructor
  · intro h; subst h; exact flip_flip σ i
  · intro h; subst h; exact flip_flip τ i

/-! ## 全配位の列挙 -/

theorem mem_allConfigs : ∀ {n : Nat} (σ : Config n), σ ∈ allConfigs n
  | 0, σ => by
    have : σ = #v[] := Vector.ext fun i h => absurd h (Nat.not_lt_zero i)
    subst this
    exact List.mem_singleton.2 rfl
  | n + 1, σ => by
    rw [← Vector.push_pop_back σ]
    simp only [allConfigs, List.mem_flatMap]
    refine ⟨σ.pop, mem_allConfigs σ.pop, ?_⟩
    cases σ.back <;> simp

theorem push_inj {n : Nat} {v w : Config n} {a b : Bool} (h : v.push a = w.push b) : v = w ∧ a = b := by
  constructor
  · apply Vector.ext
    intro i hi
    have := congrArg (fun u : Config (n + 1) => u[i]'(Nat.lt_succ_of_lt hi)) h
    simpa [Vector.getElem_push_lt hi] using this
  · have := congrArg (fun u : Config (n + 1) => u[n]'(Nat.lt_succ_self n)) h
    simpa using this

theorem nodup_allConfigs : ∀ (n : Nat), (allConfigs n).Nodup
  | 0 => List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | n + 1 => by
    simp only [allConfigs, List.Nodup]
    rw [List.pairwise_flatMap]
    refine ⟨fun v _ => ?_, ?_⟩
    · refine List.pairwise_pair.2 ?_
      intro h
      exact Bool.false_ne_true (push_inj h).2
    · refine List.Pairwise.imp ?_ (nodup_allConfigs n)
      intro v w hvw u hu u' hu' heq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hu'
      rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;>
        exact hvw (push_inj heq).1

/-! ## `Rat` のリストの和 -/

theorem sum_nonneg : ∀ {l : List Rat}, (∀ a ∈ l, 0 ≤ a) → 0 ≤ l.sum
  | [], _ => Rat.le_refl
  | a :: l, h => by
    rw [List.sum_cons]
    exact Rat.add_nonneg (h a (List.mem_cons_self ..))
      (sum_nonneg fun b hb => h b (List.mem_cons_of_mem a hb))

theorem le_sum_of_mem : ∀ {l : List Rat} {a : Rat}, (∀ b ∈ l, 0 ≤ b) → a ∈ l → a ≤ l.sum
  | [], _, _, h => absurd h List.not_mem_nil
  | b :: l, a, h, ha => by
    rw [List.sum_cons]
    have hb : 0 ≤ b := h b (List.mem_cons_self ..)
    have hl : 0 ≤ l.sum := sum_nonneg fun c hc => h c (List.mem_cons_of_mem b hc)
    rcases List.mem_cons.1 ha with rfl | ha
    · grind
    · have := le_sum_of_mem (fun c hc => h c (List.mem_cons_of_mem b hc)) ha
      grind

theorem sum_pos_of_mem {l : List Rat} {a : Rat} (h : ∀ b ∈ l, 0 ≤ b) (ha : a ∈ l) (hpos : 0 < a) :
    0 < l.sum := by
  have := le_sum_of_mem h ha
  grind

theorem sum_map_mul_left {α : Type} (c : Rat) (f : α → Rat) :
    ∀ l : List α, (l.map fun a => c * f a).sum = c * (l.map f).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_mul_left c f l]
    grind

theorem sum_map_add {α : Type} (f g : α → Rat) :
    ∀ l : List α, (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp only [List.map_nil, List.sum_nil]; grind
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_add f g l]
    grind

theorem sum_map_congr {α : Type} {f g : α → Rat} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → (l.map f).sum = (l.map g).sum
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [h a (List.mem_cons_self ..), sum_map_congr fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem sum_map_zero {α : Type} : ∀ (l : List α), (l.map fun _ => (0 : Rat)).sum = 0
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_zero l]; grind

/-- 和の順序交換。 -/
theorem sum_comm {α β : Type} (f : α → β → Rat) :
    ∀ (l₁ : List α) (l₂ : List β),
      (l₁.map fun a => (l₂.map fun b => f a b).sum).sum =
        (l₂.map fun b => (l₁.map fun a => f a b).sum).sum
  | [], l₂ => by simp only [List.map_nil, List.sum_nil]; exact (sum_map_zero l₂).symm
  | a :: l₁, l₂ => by
    simp only [List.map_cons, List.sum_cons]
    rw [sum_comm f l₁ l₂, ← sum_map_add]

/-- 重複のないリスト上で、ある 1 点 `c` だけで値をもつ関数の和。 -/
theorem sum_ite_eq {α : Type} [DecidableEq α] (v : Rat) (c : α) :
    ∀ {l : List α}, l.Nodup → c ∈ l → (l.map fun a => if a = c then v else 0).sum = v
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, hnd, hc => by
    simp only [List.map_cons, List.sum_cons]
    have hnd' := List.nodup_cons.1 hnd
    by_cases hac : a = c
    · subst hac
      rw [sum_map_congr (g := fun _ => 0) (fun b hb => by
        have : b ≠ a := fun h => hnd'.1 (h ▸ hb)
        simp [this])]
      rw [sum_map_zero]; simp only [ite_true]; grind
    · rcases List.mem_cons.1 hc with h | h
      · exact absurd h.symm hac
      · rw [sum_ite_eq v c hnd'.2 h]; simp only [hac, ite_false]; grind

theorem natCast_sum {α : Type} (f : α → Nat) :
    ∀ l : List α, (((l.map f).sum : Nat) : Rat) = (l.map fun a => (f a : Rat)).sum
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, Rat.natCast_add, natCast_sum f l]

/-! ## `Rat` の補題 -/

theorem pow_pos' {x : Rat} (hx : 0 < x) (k : Nat) : 0 < x ^ k := Rat.pow_pos hx

theorem pow_le_one' {x : Rat} (h0 : 0 ≤ x) (h1 : x ≤ 1) : ∀ k : Nat, x ^ k ≤ 1
  | 0 => by simp
  | k + 1 => by
    rw [Rat.pow_succ]
    have := pow_le_one' h0 h1 k
    have : 0 ≤ x ^ k := Rat.pow_nonneg h0
    have := Rat.mul_le_mul_of_nonneg_left h1 this
    grind

theorem pow_lt_one' {x : Rat} (h0 : 0 ≤ x) (h1 : x < 1) : ∀ {k : Nat}, 0 < k → x ^ k < 1
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | k + 1, _ => by
    rw [Rat.pow_succ]
    have hk := pow_le_one' h0 (Rat.le_of_lt h1) k
    have : 0 ≤ x ^ k := Rat.pow_nonneg h0
    have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h1) this
    have := Rat.mul_le_mul_of_nonneg_right hk h0
    grind

theorem pow_add' (x : Rat) (a b : Nat) : x ^ (a + b) = x ^ a * x ^ b :=
  Lean.Grind.Semiring.pow_add x a b

/-- `a > 0` なら `a · min(1, b / a) = min(a, b)`。 -/
theorem mul_min_div {a b : Rat} (ha : 0 < a) : a * min 1 (b / a) = min a b := by
  rw [Rat.min_def, Rat.min_def]
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  have hdiv : a * (b / a) = b := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hne
  by_cases h : (1 : Rat) ≤ b / a
  · have hab : a ≤ b := by
      have := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt ha)
      grind
    simp only [h, hab, ↓reduceIte]
    grind
  · have hlt : b / a < 1 := Rat.not_le.1 h
    have hba : b < a := by
      have := (Rat.div_lt_iff ha).1 hlt
      grind
    have hab : ¬ a ≤ b := Rat.not_le.2 hba
    simp only [h, hab, ↓reduceIte, hdiv]

end LeanIsing.Proofs
