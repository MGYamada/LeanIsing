import Proofs.DetailedBalance

/-!
# 既約性とエルゴード性

任意の正の重み `w` について、Metropolis 核 `metropolis w` が次を満たすことを証明する。

* **既約性**：どの配位 `σ` からどの配位 `τ` へも、食い違うスピンを 1 個ずつ反転していけば
  `n` ステップ以内に正の確率で移れる。各反転の受理確率 `min(1, w(σ')/w(σ))` は `w > 0` だから正。
* **エルゴード性**：ある配位 `σ₀` とサイト `i₀` で `w(flip σ₀ i₀) < w(σ₀)`（その反転は確率 1 未満でしか
  受理されない）なら、`σ₀` にとどまる確率が正になる。そこで `σ → σ₀`（`d₁ ≤ n` ステップ）、
  `σ₀` で `m - d₁ - d₂` ステップ足踏み、`σ₀ → τ`（`d₂ ≤ n` ステップ）とつなげば、
  `m ≥ 2n` のどの `m` についても `P^m(σ → τ) > 0`。これは連鎖が既約かつ非周期的であることを意味する。

古典 Ising 模型では、`0 < x < 1` で自己ループでないボンド `(u, v)` があれば、全上向き配位で `u` を
反転すると重みが減るので、この条件が満たされる。
-/

namespace LeanIsing.Proofs

/-! ## 道 -/

section Paths

variable {n : Nat}

theorem pow_nonneg {P : Config n → Config n → Rat} (hP : ∀ σ τ, 0 ≤ P σ τ) :
    ∀ (m : Nat) (σ τ : Config n), 0 ≤ Chain.pow P m σ τ
  | 0, σ, τ => by
    unfold Chain.pow
    split
    · decide
    · decide
  | m + 1, σ, τ => by
    unfold Chain.pow
    exact sum_nonneg fun a ha => by
      obtain ⟨ρ, _, rfl⟩ := List.mem_map.1 ha
      exact Rat.mul_nonneg (hP σ ρ) (pow_nonneg hP m ρ τ)

/-- 遷移行列 `P` で正の確率の遷移だけをたどる、ちょうど `m` ステップの道。 -/
inductive Path (P : Config n → Config n → Rat) : Nat → Config n → Config n → Prop
  | nil (σ : Config n) : Path P 0 σ σ
  | cons {m : Nat} {σ ρ τ : Config n} : 0 < P σ ρ → Path P m ρ τ → Path P (m + 1) σ τ

theorem Path.append {P : Config n → Config n → Rat} {a b : Nat} {σ ρ τ : Config n}
    (p : Path P a σ ρ) (q : Path P b ρ τ) : Path P (a + b) σ τ := by
  induction p with
  | nil => rw [Nat.zero_add]; exact q
  | cons h _ ih =>
    rw [Nat.add_right_comm]
    exact Path.cons h (ih q)

/-- 道があれば `m` ステップの遷移確率は正。 -/
theorem Path.pos {P : Config n → Config n → Rat} (hP : ∀ σ τ, 0 ≤ P σ τ) {m : Nat}
    {σ τ : Config n} (p : Path P m σ τ) : 0 < Chain.pow P m σ τ := by
  induction p with
  | nil σ => simp only [Chain.pow, ↓reduceIte]; decide
  | @cons m σ ρ τ h _ ih =>
    unfold Chain.pow
    refine sum_pos_of_mem (a := P σ ρ * Chain.pow P m ρ τ) ?_ ?_ ?_
    · intro a ha
      obtain ⟨ρ', _, rfl⟩ := List.mem_map.1 ha
      exact Rat.mul_nonneg (hP σ ρ') (pow_nonneg hP m ρ' τ)
    · exact List.mem_map_of_mem (mem_allConfigs ρ)
    · exact Rat.mul_pos h ih

theorem path_loops {P : Config n → Config n → Rat} {σ : Config n} (h : 0 < P σ σ) :
    ∀ s : Nat, Path P s σ σ
  | 0 => Path.nil σ
  | s + 1 => Path.cons h (path_loops h s)

end Paths

/-! ## 一般の重みの Metropolis 核 -/

section General

variable {n : Nat} {w : Config n → Rat}

theorem n_pos_of_fin (i : Fin n) : (0 : Rat) < n :=
  Rat.natCast_pos.2 (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)

/-- サイト `i` の和の項が正なら遷移確率は正。 -/
theorem metropolis_pos_of_term (hw : ∀ σ, 0 < w σ) {σ τ : Config n} (i : Fin n)
    (h : 0 < term w σ τ i) : 0 < metropolis w σ τ := by
  rw [metropolis_eq]
  have hs : 0 < ((List.finRange n).map (term w σ τ)).sum :=
    sum_pos_of_mem
      (fun a ha => by obtain ⟨j, _, rfl⟩ := List.mem_map.1 ha; exact term_nonneg hw σ τ j)
      (List.mem_map_of_mem (List.mem_finRange i)) h
  exact (Rat.lt_div_iff (n_pos_of_fin i)).2 (by grind)

/-- スピン 1 個の反転は正の確率で起こる。 -/
theorem metropolis_flip_pos (hw : ∀ σ, 0 < w σ) (σ : Config n) (i : Fin n) :
    0 < metropolis w σ (flip σ i) := by
  refine metropolis_pos_of_term hw i ?_
  have hne : σ ≠ flip σ i := fun h => flip_ne σ i h.symm
  unfold term
  simp only [hne, ↓reduceIte]
  have := acceptW_pos hw σ i
  grind

/-- 補助定理：`σ` と `τ` が食い違うサイトがすべて `l` に含まれるなら、`l.length` ステップ以内の道がある。 -/
theorem path_of_cover (hw : ∀ σ, 0 < w σ) (τ : Config n) :
    ∀ (l : List (Fin n)) (σ : Config n),
      (∀ j : Fin n, σ[(j : Nat)] ≠ τ[(j : Nat)] → j ∈ l) → ∃ d ≤ l.length, Path (metropolis w) d σ τ
  | [], σ, h => by
    have : σ = τ := Vector.ext fun k hk =>
      Classical.byContradiction fun hne => List.not_mem_nil (h ⟨k, hk⟩ hne)
    subst this
    exact ⟨0, Nat.zero_le _, Path.nil σ⟩
  | i :: l, σ, h => by
    by_cases hi : σ[(i : Nat)] = τ[(i : Nat)]
    · obtain ⟨d, hd, p⟩ := path_of_cover hw τ l σ fun j hj => by
        rcases List.mem_cons.1 (h j hj) with rfl | hjl
        · exact absurd hi hj
        · exact hjl
      exact ⟨d, Nat.le_succ_of_le hd, p⟩
    · obtain ⟨d, hd, p⟩ := path_of_cover hw τ l (flip σ i) fun j hj => by
        by_cases hji : j = i
        · subst hji
          rw [flip_get_self] at hj
          cases hσ : σ[(j : Nat)] <;> cases hτ : τ[(j : Nat)] <;> simp_all
        · have hne : (i : Nat) ≠ j := fun e => hji (Fin.ext e.symm)
          rw [flip_get_ne σ hne] at hj
          rcases List.mem_cons.1 (h j hj) with rfl | hjl
          · exact absurd rfl hji
          · exact hjl
      exact ⟨d + 1, Nat.succ_le_succ hd, Path.cons (metropolis_flip_pos hw σ i) p⟩

/-- どの 2 配位の間にも、`n` ステップ以内の正の確率の道がある。 -/
theorem path_exists (hw : ∀ σ, 0 < w σ) (σ τ : Config n) :
    ∃ d ≤ n, Path (metropolis w) d σ τ := by
  obtain ⟨d, hd, p⟩ := path_of_cover hw τ (List.finRange n) σ fun j _ => List.mem_finRange j
  rw [List.length_finRange] at hd
  exact ⟨d, hd, p⟩

/-- **既約性（一般の重み、強い形）**：どの `σ` からどの `τ` へも `n` ステップ以内に正の確率で移れる。 -/
theorem general_irreducible_within (w : Config n → Rat) (hw : ∀ σ, 0 < w σ) :
    ∀ σ τ : Config n, ∃ m ≤ n, 0 < Chain.pow (metropolis w) m σ τ := by
  intro σ τ
  obtain ⟨d, hd, p⟩ := path_exists hw σ τ
  exact ⟨d, hd, p.pos (metropolis_nonneg hw)⟩

/-- **既約性（一般の重み）**。 -/
theorem general_irreducible (w : Config n → Rat) (hw : ∀ σ, 0 < w σ) :
    Chain.Irreducible (metropolis w) := fun σ τ =>
  let ⟨m, _, h⟩ := general_irreducible_within w hw σ τ
  ⟨m, h⟩

/-- 重みが減る反転があれば、その配位にとどまる確率は正。 -/
theorem metropolis_self_pos (hw : ∀ σ, 0 < w σ) {σ₀ : Config n} {i₀ : Fin n}
    (hrej : w (flip σ₀ i₀) < w σ₀) : 0 < metropolis w σ₀ σ₀ := by
  refine metropolis_pos_of_term hw i₀ ?_
  have hlt : acceptW w σ₀ i₀ < 1 := by
    unfold acceptW
    have : w (flip σ₀ i₀) / w σ₀ < 1 := (Rat.div_lt_iff (hw σ₀)).2 (by grind)
    rw [Rat.min_def]; split <;> grind
  unfold term
  simp only [flip_ne, ↓reduceIte]
  grind

/-- **エルゴード性（一般の重み、強い形）**：重みが減る反転が 1 つでもあれば、
`m ≥ 2n` のどの `m` についても、どの `σ` からどの `τ` へもちょうど `m` ステップで正の確率で移れる。 -/
theorem general_ergodic_from (w : Config n → Rat) (hw : ∀ σ, 0 < w σ)
    (hrej : ∃ σ₀ i₀, w (flip σ₀ i₀) < w σ₀) :
    ∀ m, 2 * n ≤ m → ∀ σ τ : Config n, 0 < Chain.pow (metropolis w) m σ τ := by
  intro m hm σ τ
  obtain ⟨σ₀, i₀, h₀⟩ := hrej
  have hloop := metropolis_self_pos hw h₀
  obtain ⟨d₁, hd₁, p₁⟩ := path_exists hw σ σ₀
  obtain ⟨d₂, hd₂, p₂⟩ := path_exists hw σ₀ τ
  have p := (p₁.append (path_loops hloop (m - d₁ - d₂))).append p₂
  have e : d₁ + (m - d₁ - d₂) + d₂ = m := by omega
  rw [e] at p
  exact p.pos (metropolis_nonneg hw)

/-- **エルゴード性（一般の重み）**。 -/
theorem general_ergodic (w : Config n → Rat) (hw : ∀ σ, 0 < w σ)
    (hrej : ∃ σ₀ i₀, w (flip σ₀ i₀) < w σ₀) : Chain.Ergodic (metropolis w) :=
  ⟨2 * n, general_ergodic_from w hw hrej (2 * n) (Nat.le_refl _)⟩

end General

/-! ## 古典 Ising 模型 -/

variable {G : Graph} {x : Rat}

/-- **既約性**（強い形）：任意のグラフ、任意の `x > 0` で、`n` ステップ以内に正の確率で移れる。 -/
theorem irreducible_within (G : Graph) (x : Rat) (hx : 0 < x) :
    ∀ σ τ : Config G.n, ∃ m ≤ G.n, 0 < Chain.pow (kernel G x) m σ τ :=
  general_irreducible_within (weight G x) (weight_pos hx)

/-- **既約性**。 -/
theorem irreducible (G : Graph) (x : Rat) (hx : 0 < x) : Chain.Irreducible (kernel G x) :=
  general_irreducible (weight G x) (weight_pos hx)

theorem allUp_get {n : Nat} (k : Nat) (hk : k < n) : (allUp n)[k] = true := by
  simp [allUp]

theorem unsat_allUp : G.unsat (allUp G.n) = 0 := by
  unfold Graph.unsat
  rw [List.countP_eq_zero]
  intro b _
  simp [allUp_get]

theorem unsat_flip_allUp_pos {u v : Fin G.n} (hb : (u, v) ∈ G.bonds) (huv : u ≠ v) :
    0 < G.unsat (flip (allUp G.n) u) := by
  unfold Graph.unsat
  rw [List.countP_pos_iff]
  refine ⟨(u, v), hb, ?_⟩
  have hne : (u : Nat) ≠ v := fun e => huv (Fin.ext e)
  simp only [Fin.getElem_fin, flip_get_self, flip_get_ne _ hne, allUp_get]
  decide

/-- `0 < x < 1` なら、全上向き配位でボンドの端点 `u` を反転すると重みが減る。 -/
theorem weight_flip_allUp_lt (hx0 : 0 < x) (hx1 : x < 1) {u v : Fin G.n} (hb : (u, v) ∈ G.bonds)
    (huv : u ≠ v) : weight G x (flip (allUp G.n) u) < weight G x (allUp G.n) := by
  unfold weight
  rw [unsat_allUp, Rat.pow_zero]
  exact pow_lt_one' (Rat.le_of_lt hx0) hx1 (unsat_flip_allUp_pos hb huv)

/-- **エルゴード性**（強い形）：`0 < x < 1` で自己ループでないボンドがあれば、
`m ≥ 2n` のどの `m` についても、どの `σ` からどの `τ` へもちょうど `m` ステップで正の確率で移れる。 -/
theorem ergodic_from (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    ∀ m, 2 * G.n ≤ m → ∀ σ τ : Config G.n, 0 < Chain.pow (kernel G x) m σ τ := by
  obtain ⟨⟨u, v⟩, hb, huv⟩ := hG
  exact general_ergodic_from (weight G x) (weight_pos hx0)
    ⟨allUp G.n, u, weight_flip_allUp_lt hx0 hx1 hb huv⟩

/-- **エルゴード性**。 -/
theorem ergodic (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) : Chain.Ergodic (kernel G x) :=
  ⟨2 * G.n, ergodic_from G x hx0 hx1 hG (2 * G.n) (Nat.le_refl _)⟩

end LeanIsing.Proofs
