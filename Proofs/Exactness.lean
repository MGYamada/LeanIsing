import LeanIsing.Engine
import Proofs.DetailedBalance

/-!
# 実装の厳密性

シミュレーションが実際に動かしているマルコフ連鎖が、仕様の Metropolis 核に**厳密に**等しいことを証明する。

1. **局所エネルギー差**（`unsat_flip`）：サイト `i` を反転すると、不満足ボンドの数は
   `agree - disagree` だけ増える（`unsat(flip σ i) + disagree = unsat σ + agree`）。
2. **受理確率の一致**（`acceptLocal_eq`）：`0 < x ≤ 1` なら、近傍だけから計算した
   `acceptLocal` は仕様の `accept = min(1, w(σ')/w(σ))` に等しい。
3. **乱数格子での厳密な計数**（`count_site`）：`x.den ^ (次数) ∣ D` なら受理確率 `A` に対して
   `A · D` は整数で、`k ∈ {0, …, D-1}` のうち `k / D < A` を満たすものはちょうど `A · D` 個。
   浮動小数点の丸めがないので、受理確率は近似ではなく厳密に再現される。
4. **遷移確率の一致**（`inducedKernel_eq`）：一様な乱数 `(i, k)` に対して `step` が引き起こす遷移確率
   `inducedKernel` は仕様の `kernel` に等しい。`Sim.make` が選ぶ `D` がこの条件を満たすこと（`simulation_exact`）は `Proofs.Theorems` で示す。
-/

namespace LeanIsing.Proofs

open Engine

/-! ## 1. 局所エネルギー差 -/

theorem countP_add_congr {α : Type} {p q p' q' : α → Bool} : ∀ {l : List α},
    (∀ a ∈ l, ((if p a then 1 else 0) + (if q a then 1 else 0) : Nat) =
      (if p' a then 1 else 0) + (if q' a then 1 else 0)) →
    l.countP p + l.countP q = l.countP p' + l.countP q'
  | [], _ => rfl
  | a :: l, h => by
    have ih := countP_add_congr (l := l) fun b hb => h b (List.mem_cons_of_mem a hb)
    have ha := h a (List.mem_cons_self ..)
    simp only [List.countP_cons]
    omega

theorem unsat_flip_bond {n : Nat} (σ : Config n) (i : Fin n) (b : Fin n × Fin n) :
    ((if ((flip σ i)[b.1] != (flip σ i)[b.2]) = true then 1 else 0) +
      (if ((Option.map (fun j => σ[j] != σ[i])
        (if b.1 = i ∧ b.2 ≠ i then some b.2 else if b.2 = i ∧ b.1 ≠ i then some b.1 else none)).getD
          false) = true then 1 else 0) : Nat) =
    (if (σ[b.1] != σ[b.2]) = true then 1 else 0) +
      (if ((Option.map (fun j => σ[j] == σ[i])
        (if b.1 = i ∧ b.2 ≠ i then some b.2 else if b.2 = i ∧ b.1 ≠ i then some b.1 else none)).getD
          false) = true then 1 else 0) := by
  obtain ⟨u, v⟩ := b
  simp only [Fin.getElem_fin]
  by_cases hu : u = i <;> by_cases hv : v = i
  · subst hu; subst hv
    simp
  · subst hu
    have hne : (u : Nat) ≠ v := fun e => hv (Fin.ext e).symm
    simp only [flip_get_self, flip_get_ne σ hne]
    simp [hv]
    generalize σ[(u : Nat)] = a
    generalize σ[(v : Nat)] = b
    cases a <;> cases b <;> simp
  · subst hv
    have hne : (v : Nat) ≠ u := fun e => hu (Fin.ext e).symm
    simp only [flip_get_self, flip_get_ne σ hne]
    simp [hu]
    generalize σ[(u : Nat)] = a
    generalize σ[(v : Nat)] = b
    cases a <;> cases b <;> simp
  · have hne : (i : Nat) ≠ u := fun e => hu (Fin.ext e).symm
    have hne' : (i : Nat) ≠ v := fun e => hv (Fin.ext e).symm
    simp [hu, hv, flip_get_ne σ hne, flip_get_ne σ hne']

theorem unsat_flip (G : Graph) (σ : Config G.n) (i : Fin G.n) :
    G.unsat (flip σ i) + disagree (G.nbrs i) σ i = G.unsat σ + agree (G.nbrs i) σ i := by
  unfold Graph.unsat Graph.nbrs agree disagree
  rw [List.countP_filterMap, List.countP_filterMap]
  exact countP_add_congr fun b _ => unsat_flip_bond σ i b

/-! ## 2. 受理確率の一致 -/

variable {G : Graph} {x : Rat}

theorem acceptLocal_eq (hx0 : 0 < x) (hx1 : x ≤ 1) (σ : Config G.n) (i : Fin G.n) :
    acceptLocal x (G.nbrs i) σ i = acceptW (weight G x) σ i := by
  have key := unsat_flip G σ i
  unfold acceptLocal acceptW weight
  generalize agree (G.nbrs i) σ i = a at key ⊢
  generalize disagree (G.nbrs i) σ i = d at key ⊢
  generalize G.unsat (flip σ i) = U' at key ⊢
  generalize G.unsat σ = U at key ⊢
  have hpos : 0 < x ^ U' := Rat.pow_pos hx0
  have hposU : 0 < x ^ U := Rat.pow_pos hx0
  simp only
  split
  · -- `a ≤ d`：反転で不満足ボンドは減るか変わらない
    rename_i had
    have e : U = U' + (d - a) := by omega
    have hle : x ^ (d - a) ≤ 1 := pow_le_one' (Rat.le_of_lt hx0) hx1 _
    have hnot : ¬ x ^ U' / x ^ U < 1 := by
      rw [Rat.div_lt_iff hposU, e, pow_add']
      have := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt hpos)
      grind
    rw [Rat.min_def]
    split
    · rfl
    · rename_i h; exact absurd (Rat.not_le.1 h) hnot
  · -- `a > d`：反転で不満足ボンドが `a - d` 本増える
    rename_i had
    have e : U' = U + (a - d) := by omega
    have hdiv : x ^ U' / x ^ U = x ^ (a - d) := by
      rw [e, pow_add', Rat.mul_comm]
      exact Rat.mul_div_cancel (Rat.ne_of_gt hposU)
    rw [hdiv, Rat.min_def]
    have hle : x ^ (a - d) ≤ 1 := pow_le_one' (Rat.le_of_lt hx0) hx1 _
    split
    · rename_i h; exact Rat.le_antisymm hle h
    · rfl

/-! ## 3. 乱数格子での厳密な計数 -/

theorem mul_den_eq_num (q : Rat) : q * q.den = q.num := by
  have h : (q.den : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.2 q.den_pos)
  have e : q = (q.num : Rat) / (q.den : Rat) := by
    conv => lhs; rw [← Rat.num_divInt_den q]
    rw [Rat.divInt_eq_div, Rat.intCast_natCast]
  calc q * (q.den : Rat) = ((q.num : Rat) / q.den) * q.den := congrArg (· * (q.den : Rat)) e
    _ = q.num := Rat.div_mul_cancel h

/-- `0 ≤ r ≤ 1` で `r.den ∣ D` なら、`r · D` は `D` 以下の自然数。 -/
theorem mul_nat_of_den_dvd {r : Rat} (h0 : 0 ≤ r) (h1 : r ≤ 1) {D : Nat} (hD : r.den ∣ D) :
    ∃ c : Nat, r * D = c ∧ c ≤ D := by
  obtain ⟨E, hE⟩ := hD
  have hnum : 0 ≤ r.num := Rat.num_nonneg.2 h0
  refine ⟨r.num.toNat * E, ?_, ?_⟩
  · rw [hE, Rat.natCast_mul, Rat.natCast_mul, ← Rat.mul_assoc, mul_den_eq_num,
      ← Rat.intCast_natCast r.num.toNat, Int.toNat_of_nonneg hnum]
  · have hr : r * D ≤ 1 * D := Rat.mul_le_mul_of_nonneg_right h1 Rat.natCast_nonneg
    have : ((r.num.toNat * E : Nat) : Rat) ≤ D := by
      have e : r * D = ((r.num.toNat * E : Nat) : Rat) := by
        rw [hE, Rat.natCast_mul, Rat.natCast_mul, ← Rat.mul_assoc, mul_den_eq_num,
          ← Rat.intCast_natCast r.num.toNat, Int.toNat_of_nonneg hnum]
      rw [← e]; grind
    exact Rat.natCast_le_natCast.1 this

theorem agree_le_length {n : Nat} (nb : List (Fin n)) (σ : Config n) (i : Fin n) :
    agree nb σ i ≤ nb.length := List.countP_le_length

/-- 受理確率 `A` について、`A · D` は `D` 以下の自然数。 -/
theorem acceptLocal_mul_nat (hx0 : 0 < x) (hx1 : x ≤ 1) {D : Nat}
    (σ : Config G.n) (i : Fin G.n) (hD : x.den ^ (G.nbrs i).length ∣ D) :
    ∃ c : Nat, acceptLocal x (G.nbrs i) σ i * D = c ∧ c ≤ D := by
  unfold acceptLocal
  simp only
  split
  · exact ⟨D, by grind, Nat.le_refl D⟩
  · refine mul_nat_of_den_dvd (Rat.pow_nonneg (Rat.le_of_lt hx0))
      (pow_le_one' (Rat.le_of_lt hx0) hx1 _) ?_
    rw [Rat.den_pow]
    refine Nat.dvd_trans (Nat.pow_dvd_pow _ ?_) hD
    have := agree_le_length (G.nbrs i) σ i
    omega

theorem countP_lt_range (c : Nat) : ∀ D : Nat,
    (List.range D).countP (fun k => decide (k < c)) = min c D
  | 0 => by simp
  | D + 1 => by
    rw [List.range_succ, List.countP_append, countP_lt_range c D]
    simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
    split <;> omega

/-- `A · D = c` なら、`k ∈ {0, …, D - 1}` のうち `k / D < A` となるのは `min(c, D)` 個。 -/
theorem countP_div_lt {D c : Nat} (hD : 0 < D) {A : Rat} (hA : A * D = c) :
    (List.range D).countP (fun k : Nat => decide ((k : Rat) / D < A)) = min c D := by
  rw [← countP_lt_range c D]
  apply List.countP_congr
  intro k _
  have hDpos : (0 : Rat) < D := Rat.natCast_pos.2 hD
  simp only [decide_eq_true_eq]
  rw [Rat.div_lt_iff hDpos, hA, Rat.natCast_lt_natCast]

theorem natCast_sub' {a b : Nat} (h : b ≤ a) : ((a - b : Nat) : Rat) = a - b := by
  have : ((a - b : Nat) : Rat) + b = a := by rw [← Rat.natCast_add, Nat.sub_add_cancel h]
  grind

/-- **しきい値判定の計数**：`A · D = c`（`c ≤ D` は自然数）なら、`k ∈ {0, …, D - 1}` のうち
「`k / D < A` なら `flip σ i`、さもなくば `σ`」が `τ` になるものの数は `D · ([flip σ i = τ] A + [σ = τ] (1 - A))`。
受理確率の計算方法によらない（古典模型と層つき模型の両方で使う）。 -/
theorem count_threshold {n : Nat} {D c : Nat} (hDpos : 0 < D) {A : Rat} (hc : A * D = c)
    (hcD : c ≤ D) (σ τ : Config n) (i : Fin n) :
    (((List.range D).countP fun k : Nat =>
        decide ((if (k : Rat) / D < A then flip σ i else σ) = τ) : Nat) : Rat) =
      D * ((if flip σ i = τ then A else 0) + (if σ = τ then 1 - A else 0)) := by
  have hcount := countP_div_lt hDpos hc
  rw [Nat.min_eq_left hcD] at hcount
  by_cases hf : flip σ i = τ
  · -- 受理されたときだけ `τ` に移る
    have hne : σ ≠ τ := fun h => flip_ne σ i (hf.trans h.symm)
    rw [List.countP_congr (q := fun k : Nat => decide ((k : Rat) / D < A)) (fun k _ => by
      by_cases hk : (k : Rat) / D < A
      · simp [hk, hf]
      · simp [hk, hne]), hcount]
    simp only [hf, hne, ↓reduceIte]
    grind
  · by_cases hst : σ = τ
    · -- 棄却されたときだけ `τ = σ` にとどまる
      subst hst
      have hlen := List.length_eq_countP_add_countP
        (fun k : Nat => decide ((k : Rat) / D < A)) (l := List.range D)
      rw [List.length_range, hcount] at hlen
      rw [List.countP_congr (q := fun k : Nat => decide ¬ (decide ((k : Rat) / D < A)) = true)
        (fun k _ => by
          by_cases hk : (k : Rat) / D < A
          · simp [hk, hf]
          · simp [hk])]
      have : List.countP (fun k : Nat => decide ¬ (decide ((k : Rat) / D < A)) = true)
          (List.range D) = D - c := by omega
      rw [this, natCast_sub' hcD]
      simp only [hf, ↓reduceIte]
      grind
    · -- どちらにも移らない
      rw [List.countP_eq_zero.2 (fun k _ => by
        by_cases hk : (k : Rat) / D < A
        · simp [hk, hf]
        · simp [hk, hst])]
      simp only [hf, hst, ↓reduceIte]
      grind

/-- サイト `i` を選んだとき、`D` 通りの `u = k / D` のうち `σ` を `τ` に移すものの数は `D · term`。 -/
theorem count_site (hx0 : 0 < x) (hx1 : x ≤ 1) {D : Nat} (hDpos : 0 < D)
    (σ τ : Config G.n) (i : Fin G.n) (hD : x.den ^ (G.nbrs i).length ∣ D) :
    (((List.range D).countP fun k : Nat =>
        decide (step x (G.nbrs i) σ i ((k : Rat) / D) = τ) : Nat) : Rat) =
      D * term (weight G x) σ τ i := by
  obtain ⟨c, hc, hcD⟩ := acceptLocal_mul_nat hx0 hx1 σ i hD
  unfold step term
  rw [← acceptLocal_eq hx0 hx1 σ i]
  exact count_threshold hDpos hc hcD σ τ i

/-! ## 4. 遷移確率の一致 -/

/-- **実装の厳密性**：`0 < x ≤ 1` で、各サイトについて `x.den ^ (次数) ∣ D` なら、
一様乱数 `(i, k)` に対して `step` が引き起こす遷移確率は仕様の Metropolis 核に厳密に等しい。 -/
theorem inducedKernel_eq (hx0 : 0 < x) (hx1 : x ≤ 1) {D : Nat} (hDpos : 0 < D)
    (hD : ∀ i : Fin G.n, x.den ^ (G.nbrs i).length ∣ D) (σ τ : Config G.n) :
    inducedKernel G x D σ τ = kernel G x σ τ := by
  unfold inducedKernel
  rw [kernel_eq, natCast_sum, sum_map_congr (fun i _ => count_site hx0 hx1 hDpos σ τ i (hD i)),
    sum_map_mul_left]
  have hD0 : (D : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.2 hDpos)
  generalize ((List.finRange G.n).map (term (weight G x) σ τ)).sum = S
  grind

end LeanIsing.Proofs
