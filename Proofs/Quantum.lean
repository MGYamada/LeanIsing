import LeanIsing.Quantum
import Proofs.Layered

/-!
# 横磁場 Ising 模型の経路積分量子モンテカルロ法

* `trotter_weight`：2 層の模型 `trotter G M x y` の重みは、世界線の重み
  `pathWeight = Π_τ transfer(s_τ, s_{τ+1})`（Trotter 転送行列の要素の積）に等しい。
* `transfer_eq_tensor`：`transfer(s, s') = x^{unsat(s)} · Π_i ⟨s_i|(1 + y σˣ)|s'_i⟩`。
  横磁場の因子が 1 サイトの演算子 `1 + y σˣ`（`e^{εΓσˣ} / cosh εΓ`）のテンソル積であることを表す。
* `pathWeight_one`：`M = 1` では横磁場の寄与が消え、古典模型の重みに戻る。
* `qmc_*`：シミュレーション（`Layered.Sim.make (trotter G M x y)`）が動かしている連鎖について、
  世界線の分布（経路積分の重みを規格化したもの）に関する詳細釣り合い・定常性・既約性・
  エルゴード性・幾何収束。
-/

namespace LeanIsing.Proofs

open Quantum

/-! ## 世界線の重み -/

theorem slice_get {N M : Nat} (s : Config (N * M)) (τ : Fin M) (i : Fin N) :
    (slice s τ)[(i : Nat)] = s[(idx τ i : Nat)] := by
  simp [slice]

theorem pow_sum_mul {α : Type} (x y : Rat) (f g : α → Nat) :
    ∀ l : List α, x ^ (l.map f).sum * y ^ (l.map g).sum = (l.map fun a => x ^ f a * y ^ g a).prod
  | [] => by simp only [List.map_nil, List.sum_nil, List.prod_nil, Rat.pow_zero]; grind
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add']
    rw [← pow_sum_mul x y f g l]
    grind

theorem unsat_space (G : Graph) (M : Nat) (s : Config (G.n * M)) :
    unsatOf (spaceBonds G M) s = ((List.finRange M).map fun τ => G.unsat (slice s τ)).sum := by
  unfold unsatOf spaceBonds
  rw [List.countP_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro τ _
  simp only [Function.comp, List.countP_map]
  unfold Graph.unsat
  apply List.countP_congr
  intro b _
  simp only [Function.comp, Fin.getElem_fin, slice_get]

theorem unsat_time (N M : Nat) (s : Config (N * M)) :
    unsatOf (timeBonds N M) s =
      ((List.finRange M).map fun τ => hamming (slice s τ) (slice s (next τ))).sum := by
  unfold unsatOf timeBonds
  rw [List.countP_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro τ _
  simp only [Function.comp, List.countP_map]
  unfold hamming
  apply List.countP_congr
  intro i _
  simp only [Function.comp, Fin.getElem_fin, slice_get]

/-- **経路積分の重み**：2 層の模型の重みは、Trotter 転送行列の要素の積（世界線の重み）に等しい。 -/
theorem trotter_weight_apply (G : Graph) (M : Nat) (x y : Rat) (s : Config (G.n * M)) :
    (trotter G M x y).weight s = pathWeight G M x y s := by
  show x ^ unsatOf (spaceBonds G M) s * (y ^ unsatOf (timeBonds G.n M) s * 1) = _
  rw [Rat.mul_one, unsat_space, unsat_time, pow_sum_mul]
  rfl

theorem trotter_weight (G : Graph) (M : Nat) (x y : Rat) :
    (trotter G M x y).weight = pathWeight G M x y :=
  funext fun s => trotter_weight_apply G M x y s

theorem prod_ite_pow {α : Type} (y : Rat) (p : α → Bool) :
    ∀ l : List α, (l.map fun a => if p a then (1 : Rat) else y).prod = y ^ l.countP (fun a => !p a)
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.prod_cons, List.countP_cons, prod_ite_pow y p l, pow_add']
    cases p a <;> simp <;> grind

/-- **横磁場の因子はテンソル積**：`transfer(s, s') = x^{unsat(s)} · Π_i ⟨s_i|(1 + y σˣ)|s'_i⟩`
（`⟨a|(1 + yσˣ)|b⟩ = 1`（`a = b`）、`y`（`a ≠ b`））。 -/
theorem transfer_eq_tensor (G : Graph) (x y : Rat) (s s' : Config G.n) :
    transfer G x y s s' =
      x ^ G.unsat s * ((List.finRange G.n).map fun i => if s[i] == s'[i] then 1 else y).prod := by
  unfold transfer hamming
  rw [prod_ite_pow]
  rfl

/-- **`M = 1` は古典模型**：Trotter 数 1 では虚時間方向のボンドが自己ループになり、横磁場の寄与が消える。 -/
theorem pathWeight_one (G : Graph) (x y : Rat) (s : Config (G.n * 1)) :
    pathWeight G 1 x y s = weight G x (slice s ⟨0, Nat.zero_lt_one⟩) := by
  have hnext : next (⟨0, Nat.zero_lt_one⟩ : Fin 1) = ⟨0, Nat.zero_lt_one⟩ := rfl
  have hfin : List.finRange 1 = [⟨0, Nat.zero_lt_one⟩] := by decide
  have hham : ∀ t : Config G.n, hamming t t = 0 := fun t => by
    unfold hamming; rw [List.countP_eq_zero]; intro i _; simp
  unfold pathWeight
  rw [hfin]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hnext, transfer, hham,
    Rat.pow_zero, Rat.mul_one]
  rfl

/-! ## 量子モンテカルロ法の連鎖 -/

theorem trotter_layers_mem {G : Graph} {M : Nat} {x y : Rat}
    {l : List (Fin (trotter G M x y).n × Fin (trotter G M x y).n) × Rat}
    (hl : l ∈ (trotter G M x y).layers) : l = (spaceBonds G M, x) ∨ l = (timeBonds G.n M, y) := by
  change l ∈ [(spaceBonds G M, x), (timeBonds G.n M, y)] at hl
  rcases List.mem_cons.1 hl with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_singleton.1 h)

theorem trotter_valid (G : Graph) (M : Nat) {x y : Rat} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y)
    (hy1 : y ≤ 1) : (trotter G M x y).Valid := by
  intro l hl
  rcases trotter_layers_mem hl with rfl | rfl
  · exact ⟨hx0, hx1⟩
  · exact ⟨hy0, hy1⟩

theorem idx_inj {N M : Nat} (τ : Fin M) {u v : Fin N} (h : idx τ u = idx τ v) : u = v := by
  have := congrArg Fin.val h
  simp only [idx] at this
  exact Fin.ext (by omega)

theorem trotter_frustratable (G : Graph) {M : Nat} (hM : 0 < M) {x y : Rat} (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) : (trotter G M x y).Frustratable := by
  obtain ⟨⟨u, v⟩, hb, huv⟩ := hG
  let τ₀ : Fin M := ⟨0, hM⟩
  refine ⟨(spaceBonds G M, x), List.mem_cons_self .., hx1, (idx τ₀ u, idx τ₀ v), ?_, ?_⟩
  · exact List.mem_flatMap.2 ⟨τ₀, List.mem_finRange τ₀, List.mem_map.2 ⟨(u, v), hb, rfl⟩⟩
  · exact fun h => huv (idx_inj τ₀ h)

theorem trotter_kernel (G : Graph) (M : Nat) (x y : Rat) :
    (trotter G M x y).kernel = metropolis (pathWeight G M x y) := by
  show metropolis (trotter G M x y).weight = _
  rw [trotter_weight]
  rfl

theorem trotter_boltzmann (G : Graph) (M : Nat) (x y : Rat) :
    (trotter G M x y).boltzmann = pathDistribution G M x y := by
  show normalize (trotter G M x y).weight = _
  rw [trotter_weight]; rfl

/-- **量子モンテカルロ法の実装の厳密性**：シミュレーションが動かしている連鎖の遷移確率は、
世界線の重み `pathWeight` に対する Metropolis 核に厳密に等しい。 -/
theorem qmc_exact (G : Graph) (M : Nat) {x y : Rat} (hx0 : 0 < x) (hy0 : 0 < y) :
    Layered.inducedKernel (trotter G M x y) = metropolis (pathWeight G M x y) := by
  rw [layered_exact (trotter G M x y) (fun l hl => by
      rcases trotter_layers_mem hl with rfl | rfl
      · exact hx0
      · exact hy0),
    trotter_kernel]

/-- **量子モンテカルロ法の主定理**：`0 < x < 1`、`0 < y ≤ 1`、Trotter 数 `M ≥ 1`、空間グラフに
自己ループでないボンドがあれば、シミュレーションが動かしている連鎖は世界線の分布
（経路積分の重みを規格化したもの）について詳細釣り合いを満たし、それを定常分布にもち、
エルゴード的で、任意の初期分布からそこへ幾何的に収束する。 -/
theorem qmc_simulation (G : Graph) (M : Nat) (hM : 0 < M) (x y : Rat) (hx0 : 0 < x)
    (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y ≤ 1) (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    Chain.DetailedBalance (pathDistribution G M x y) (Layered.inducedKernel (trotter G M x y)) ∧
      Chain.Stationary (pathDistribution G M x y) (Layered.inducedKernel (trotter G M x y)) ∧
      Chain.Ergodic (Layered.inducedKernel (trotter G M x y)) ∧
      Chain.GeometricConvergence (pathDistribution G M x y)
        (Layered.inducedKernel (trotter G M x y)) ∧
      Chain.Converges (pathDistribution G M x y) (Layered.inducedKernel (trotter G M x y)) := by
  have hV := trotter_valid G M hx0 (Rat.le_of_lt hx1) hy0 hy1
  have hF := trotter_frustratable G hM (y := y) hx1 hG
  have hn := Model.n_pos hF
  rw [← trotter_boltzmann]
  refine ⟨layered_simulation_detailed_balance _ hV, layered_simulation_stationary _ hV hn,
    layered_simulation_ergodic _ hV hF, layered_simulation_converges _ hV hF⟩

end LeanIsing.Proofs
