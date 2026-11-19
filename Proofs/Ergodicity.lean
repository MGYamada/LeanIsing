import Proofs.DetailedBalance

/-!
# 既約性とエルゴード性

* **既約性**（任意のグラフ、任意の `x > 0`）：どの配位 `σ` からどの配位 `τ` へも、
  食い違うスピンを 1 個ずつ反転していけば `n` ステップ以内に正の確率で移れる。
  各反転の受理確率 `min(1, w(σ')/w(σ))` は `w > 0` だから正。
* **エルゴード性**（`0 < x < 1`、自己ループでないボンドが 1 本以上）：`m ≥ 2n` のどの `m` についても、
  どの `σ` からどの `τ` へもちょうど `m` ステップで正の確率で移れる。
  全上向き配位 `↑↑…↑` では、ボンドの端点 `u` の反転で不満足ボンドが増えるので受理確率が 1 未満になり、
  その場にとどまる確率が正になる。そこで `σ → ↑↑…↑`（`d₁ ≤ n` ステップ）、
  `↑↑…↑` で `m - d₁ - d₂` ステップ足踏み、`↑↑…↑ → τ`（`d₂ ≤ n` ステップ）とつなげばよい。
  これは連鎖が既約かつ非周期的であること（有限状態での正則性）を意味する。
-/

namespace LeanIsing.Proofs

variable {G : Graph} {x : Rat}

theorem pow_nonneg (hx : 0 < x) : ∀ (m : Nat) (σ τ : Config G.n), 0 ≤ Chain.pow (kernel G x) m σ τ
  | 0, σ, τ => by
    unfold Chain.pow
    split
    · decide
    · decide
  | m + 1, σ, τ => by
    unfold Chain.pow
    exact sum_nonneg fun a ha => by
      obtain ⟨ρ, _, rfl⟩ := List.mem_map.1 ha
      exact Rat.mul_nonneg (kernel_nonneg hx σ ρ) (pow_nonneg hx m ρ τ)

/-- 正の確率の遷移だけをたどる、ちょうど `m` ステップの道。 -/
inductive Path (G : Graph) (x : Rat) : Nat → Config G.n → Config G.n → Prop
  | nil (σ : Config G.n) : Path G x 0 σ σ
  | cons {m : Nat} {σ ρ τ : Config G.n} :
      0 < kernel G x σ ρ → Path G x m ρ τ → Path G x (m + 1) σ τ

theorem Path.append {a b : Nat} {σ ρ τ : Config G.n} (p : Path G x a σ ρ) (q : Path G x b ρ τ) :
    Path G x (a + b) σ τ := by
  induction p with
  | nil => rw [Nat.zero_add]; exact q
  | cons h _ ih =>
    rw [Nat.add_right_comm]
    exact Path.cons h (ih q)

/-- 道があれば `m` ステップの遷移確率は正。 -/
theorem Path.pos (hx : 0 < x) {m : Nat} {σ τ : Config G.n} (p : Path G x m σ τ) :
    0 < Chain.pow (kernel G x) m σ τ := by
  induction p with
  | nil σ => simp only [Chain.pow, ↓reduceIte]; decide
  | @cons m σ ρ τ h _ ih =>
    unfold Chain.pow
    refine sum_pos_of_mem (a := kernel G x σ ρ * Chain.pow (kernel G x) m ρ τ) ?_ ?_ ?_
    · intro a ha
      obtain ⟨ρ', _, rfl⟩ := List.mem_map.1 ha
      exact Rat.mul_nonneg (kernel_nonneg hx σ ρ') (pow_nonneg hx m ρ' τ)
    · exact List.mem_map_of_mem (mem_allConfigs ρ)
    · exact Rat.mul_pos h ih

theorem n_pos_of_fin (i : Fin G.n) : (0 : Rat) < G.n :=
  Rat.natCast_pos.2 (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)

/-- サイト `i` の和の項が正なら遷移確率は正。 -/
theorem kernel_pos_of_term (hx : 0 < x) {σ τ : Config G.n} (i : Fin G.n)
    (h : 0 < term G x σ τ i) : 0 < kernel G x σ τ := by
  rw [kernel_eq]
  have hs : 0 < ((List.finRange G.n).map (term G x σ τ)).sum :=
    sum_pos_of_mem
      (fun a ha => by obtain ⟨j, _, rfl⟩ := List.mem_map.1 ha; exact term_nonneg hx σ τ j)
      (List.mem_map_of_mem (List.mem_finRange i)) h
  exact (Rat.lt_div_iff (n_pos_of_fin i)).2 (by grind)

/-- スピン 1 個の反転は正の確率で起こる。 -/
theorem kernel_flip_pos (hx : 0 < x) (σ : Config G.n) (i : Fin G.n) :
    0 < kernel G x σ (flip σ i) := by
  refine kernel_pos_of_term hx i ?_
  have hne : σ ≠ flip σ i := fun h => flip_ne σ i h.symm
  unfold term
  simp only [hne, ↓reduceIte]
  have := accept_pos hx σ i
  grind

/-- 補助定理：`σ` と `τ` が食い違うサイトがすべて `l` に含まれるなら、`l.length` ステップ以内の道がある。 -/
theorem path_of_cover (hx : 0 < x) (τ : Config G.n) :
    ∀ (l : List (Fin G.n)) (σ : Config G.n),
      (∀ j : Fin G.n, σ[(j : Nat)] ≠ τ[(j : Nat)] → j ∈ l) → ∃ d ≤ l.length, Path G x d σ τ
  | [], σ, h => by
    have : σ = τ := Vector.ext fun k hk =>
      Classical.byContradiction fun hne => List.not_mem_nil (h ⟨k, hk⟩ hne)
    subst this
    exact ⟨0, Nat.zero_le _, Path.nil σ⟩
  | i :: l, σ, h => by
    by_cases hi : σ[(i : Nat)] = τ[(i : Nat)]
    · obtain ⟨d, hd, p⟩ := path_of_cover hx τ l σ fun j hj => by
        rcases List.mem_cons.1 (h j hj) with rfl | hjl
        · exact absurd hi hj
        · exact hjl
      exact ⟨d, Nat.le_succ_of_le hd, p⟩
    · obtain ⟨d, hd, p⟩ := path_of_cover hx τ l (flip σ i) fun j hj => by
        by_cases hji : j = i
        · subst hji
          rw [flip_get_self] at hj
          cases hσ : σ[(j : Nat)] <;> cases hτ : τ[(j : Nat)] <;> simp_all
        · have hne : (i : Nat) ≠ j := fun e => hji (Fin.ext e.symm)
          rw [flip_get_ne σ hne] at hj
          rcases List.mem_cons.1 (h j hj) with rfl | hjl
          · exact absurd rfl hji
          · exact hjl
      exact ⟨d + 1, Nat.succ_le_succ hd, Path.cons (kernel_flip_pos hx σ i) p⟩

/-- どの 2 配位の間にも、`n` ステップ以内の正の確率の道がある。 -/
theorem path_exists (hx : 0 < x) (σ τ : Config G.n) : ∃ d ≤ G.n, Path G x d σ τ := by
  obtain ⟨d, hd, p⟩ := path_of_cover hx τ (List.finRange G.n) σ fun j _ => List.mem_finRange j
  rw [List.length_finRange] at hd
  exact ⟨d, hd, p⟩

/-- **既約性**（強い形）：任意のグラフ、任意の `x > 0` で、どの `σ` からどの `τ` へも
`n` ステップ以内に正の確率で移れる。 -/
theorem irreducible_within (G : Graph) (x : Rat) (hx : 0 < x) :
    ∀ σ τ : Config G.n, ∃ m ≤ G.n, 0 < Chain.pow (kernel G x) m σ τ := by
  intro σ τ
  obtain ⟨d, hd, p⟩ := path_exists hx σ τ
  exact ⟨d, hd, p.pos hx⟩

/-- **既約性**。 -/
theorem irreducible (G : Graph) (x : Rat) (hx : 0 < x) : Chain.Irreducible (kernel G x) := fun σ τ =>
  let ⟨m, _, h⟩ := irreducible_within G x hx σ τ
  ⟨m, h⟩

/-! ## 非周期性：全上向き配位での足踏み -/

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

/-- `0 < x < 1` なら、全上向き配位でボンドの端点 `u` を反転する受理確率は 1 未満。 -/
theorem accept_allUp_lt (hx0 : 0 < x) (hx1 : x < 1) {u v : Fin G.n} (hb : (u, v) ∈ G.bonds)
    (huv : u ≠ v) : accept G x (allUp G.n) u < 1 := by
  unfold accept weight
  rw [unsat_allUp, Rat.pow_zero]
  have e : x ^ G.unsat (flip (allUp G.n) u) / 1 = x ^ G.unsat (flip (allUp G.n) u) := by grind
  rw [e, Rat.min_def]
  have := pow_lt_one' (Rat.le_of_lt hx0) hx1 (unsat_flip_allUp_pos hb huv)
  split <;> grind

/-- 全上向き配位にとどまる確率は正。 -/
theorem kernel_allUp_self_pos (hx0 : 0 < x) (hx1 : x < 1) {u v : Fin G.n} (hb : (u, v) ∈ G.bonds)
    (huv : u ≠ v) : 0 < kernel G x (allUp G.n) (allUp G.n) := by
  refine kernel_pos_of_term hx0 u ?_
  unfold term
  simp only [flip_ne, ↓reduceIte]
  have := accept_allUp_lt hx0 hx1 hb huv
  grind

theorem path_loops {σ : Config G.n} (h : 0 < kernel G x σ σ) : ∀ s : Nat, Path G x s σ σ
  | 0 => Path.nil σ
  | s + 1 => Path.cons h (path_loops h s)

/-- **エルゴード性**（強い形）：`0 < x < 1` で自己ループでないボンドがあれば、
`m ≥ 2n` のどの `m` についても、どの `σ` からどの `τ` へもちょうど `m` ステップで正の確率で移れる。 -/
theorem ergodic_from (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    ∀ m, 2 * G.n ≤ m → ∀ σ τ : Config G.n, 0 < Chain.pow (kernel G x) m σ τ := by
  intro m hm σ τ
  obtain ⟨⟨u, v⟩, hb, huv⟩ := hG
  have hloop := kernel_allUp_self_pos hx0 hx1 hb huv
  obtain ⟨d₁, hd₁, p₁⟩ := path_exists hx0 σ (allUp G.n)
  obtain ⟨d₂, hd₂, p₂⟩ := path_exists hx0 (allUp G.n) τ
  have p := (p₁.append (path_loops hloop (m - d₁ - d₂))).append p₂
  have e : d₁ + (m - d₁ - d₂) + d₂ = m := by omega
  rw [e] at p
  exact p.pos hx0

/-- **エルゴード性**。 -/
theorem ergodic (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) : Chain.Ergodic (kernel G x) :=
  ⟨2 * G.n, ergodic_from G x hx0 hx1 hG (2 * G.n) (Nat.le_refl _)⟩

end LeanIsing.Proofs
