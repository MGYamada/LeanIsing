import LeanIsing.Lattice
import Proofs.Ergodicity
import Proofs.Exactness
import Proofs.Convergence

/-!
# 主定理

* `metropolis_*`：任意の相互作用グラフ上の Metropolis 核 `kernel G x` について、
  確率行列であること・詳細釣り合い・定常性・既約性・エルゴード性。
* `simulation_*`：シミュレーション（`Sim.make G x`）が**実際に動かしている**マルコフ連鎖
  `inducedKernel G x (Sim.make G x).D`（一様乱数 `i ∈ Fin n`、`u = k / D` に対する `step` の遷移確率）
  について、同じ性質。`simulation_exact` により仕様の核と厳密に一致するので、そこから従う。
* `*_converges` / `*_geometric`：任意の初期分布から Boltzmann 分布への（幾何）収束（`Proofs.Convergence`）。
* `square_*`：`L × L` 正方格子（周期境界、`L ≥ 2`）への適用。
* `rejection_exact`：乱数の棄却法が偏らないこと。
-/

namespace LeanIsing.Proofs

open Engine

/-! ## 任意のグラフ上の Metropolis 核 -/

theorem metropolis_stochastic (G : Graph) (x : Rat) (hx : 0 < x) (hn : 0 < G.n) :
    Chain.Stochastic (kernel G x) :=
  stochastic G x hx hn

theorem metropolis_detailed_balance (G : Graph) (x : Rat) (hx : 0 < x) :
    Chain.DetailedBalance (boltzmann G x) (kernel G x) :=
  detailed_balance G x hx

theorem metropolis_stationary (G : Graph) (x : Rat) (hx : 0 < x) (hn : 0 < G.n) :
    Chain.Stationary (boltzmann G x) (kernel G x) :=
  stationary G x hx hn

theorem metropolis_irreducible (G : Graph) (x : Rat) (hx : 0 < x) :
    Chain.Irreducible (kernel G x) :=
  irreducible G x hx

theorem metropolis_ergodic (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) : Chain.Ergodic (kernel G x) :=
  ergodic G x hx0 hx1 hG

-- `metropolis_geometric` と `metropolis_converges` は `Proofs.Convergence` にある。

/-! ## シミュレーションが動かしている連鎖 -/

theorem le_foldl_max {α : Type} (f : α → Nat) :
    ∀ (l : List α) (m₀ : Nat), m₀ ≤ l.foldl (fun m a => max m (f a)) m₀ ∧
      ∀ a ∈ l, f a ≤ l.foldl (fun m a => max m (f a)) m₀
  | [], m₀ => ⟨Nat.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | b :: l, m₀ => by
    obtain ⟨h₁, h₂⟩ := le_foldl_max f l (max m₀ (f b))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h₁, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Nat.le_trans (Nat.le_max_right _ _) h₁
    · exact h₂ a ha

theorem Sim.nbrTable_eq (G : Graph) (x : Rat) (i : Fin G.n) :
    (Sim.make G x).nbrTable[(i : Nat)]'i.isLt = G.nbrs i := by
  show (Vector.ofFn G.nbrs)[(i : Nat)] = G.nbrs i
  rw [Vector.getElem_ofFn]

theorem Sim.D_pos (G : Graph) (x : Rat) : 0 < (Sim.make G x).D :=
  Nat.pow_pos x.den_pos

/-- `Sim.make` が選ぶ分母 `D = x.den ^ (最大次数)` は、どのサイトの受理確率の分母でも割り切れる。 -/
theorem Sim.den_dvd (G : Graph) (x : Rat) (i : Fin G.n) :
    x.den ^ (G.nbrs i).length ∣ (Sim.make G x).D := by
  refine Nat.pow_dvd_pow _ ?_
  have := (le_foldl_max (fun j : Fin G.n => (Vector.ofFn G.nbrs)[j].length) (List.finRange G.n) 0).2 i
    (List.mem_finRange i)
  simpa [maxLen, Sim.make] using this

theorem Sim.stepPure_fst' (s : Sim) (σ : Config s.G.n) (i : Fin s.G.n) (k : Nat) :
    (s.stepPure σ i k).1 = step s.x s.nbrTable[i] σ i ((k : Rat) / s.D) := by
  unfold Sim.stepPure stepWithFlag step
  simp only [Rat.mkRat_eq_div, Rat.intCast_natCast]
  split <;> rfl

/-- シミュレーションの 1 ステップ（乱数 `i`、`k` を与えたとき）は、`u = k / D` に対する `step` そのもの。 -/
theorem Sim.stepPure_fst (G : Graph) (x : Rat) (σ : Config G.n) (i : Fin G.n) (k : Nat) :
    ((Sim.make G x).stepPure σ i k).1 = step x (G.nbrs i) σ i ((k : Rat) / (Sim.make G x).D) := by
  refine (Sim.stepPure_fst' (Sim.make G x) σ i k).trans ?_
  show step x (Vector.ofFn G.nbrs)[(i : Nat)] σ i _ = _
  rw [Vector.getElem_ofFn]

/-- **実装の厳密性**：シミュレーションが動かしている連鎖の遷移確率は、仕様の Metropolis 核に厳密に等しい。 -/
theorem simulation_exact (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    inducedKernel G x (Sim.make G x).D = kernel G x := by
  funext σ τ
  exact inducedKernel_eq hx0 hx1 (Sim.D_pos G x) (Sim.den_dvd G x) σ τ

theorem simulation_stochastic (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x ≤ 1) (hn : 0 < G.n) :
    Chain.Stochastic (inducedKernel G x (Sim.make G x).D) := by
  rw [simulation_exact G x hx0 hx1]; exact stochastic G x hx0 hn

/-- **詳細釣り合い（実装）**。 -/
theorem simulation_detailed_balance (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Chain.DetailedBalance (boltzmann G x) (inducedKernel G x (Sim.make G x).D) := by
  rw [simulation_exact G x hx0 hx1]; exact detailed_balance G x hx0

theorem simulation_stationary (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x ≤ 1) (hn : 0 < G.n) :
    Chain.Stationary (boltzmann G x) (inducedKernel G x (Sim.make G x).D) := by
  rw [simulation_exact G x hx0 hx1]; exact stationary G x hx0 hn

theorem simulation_irreducible (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Chain.Irreducible (inducedKernel G x (Sim.make G x).D) := by
  rw [simulation_exact G x hx0 hx1]; exact irreducible G x hx0

/-- **エルゴード性（実装）**。 -/
theorem simulation_ergodic (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    Chain.Ergodic (inducedKernel G x (Sim.make G x).D) := by
  rw [simulation_exact G x hx0 (Rat.le_of_lt hx1)]; exact ergodic G x hx0 hx1 hG

/-- **幾何収束（実装）**。 -/
theorem simulation_geometric (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    Chain.GeometricConvergence (boltzmann G x) (inducedKernel G x (Sim.make G x).D) := by
  rw [simulation_exact G x hx0 (Rat.le_of_lt hx1)]; exact metropolis_geometric G x hx0 hx1 hG

/-- **収束（実装）**：シミュレーションが動かしている連鎖は、任意の初期分布から Boltzmann 分布へ収束する。 -/
theorem simulation_converges (G : Graph) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1)
    (hG : ∃ b ∈ G.bonds, b.1 ≠ b.2) :
    Chain.Converges (boltzmann G x) (inducedKernel G x (Sim.make G x).D) := by
  rw [simulation_exact G x hx0 (Rat.le_of_lt hx1)]; exact metropolis_converges G x hx0 hx1 hG

/-! ## 正方格子 -/

/-- `L ≥ 2` の正方格子には自己ループでないボンドがある（サイト 0 とその右隣）。 -/
theorem square_has_bond {L : Nat} (hL : 2 ≤ L) :
    ∃ b ∈ (Lattice.square L).bonds, b.1 ≠ b.2 := by
  have hpos : 0 < L * L := Nat.mul_pos (by omega) (by omega)
  let s : Fin (L * L) := ⟨0, hpos⟩
  refine ⟨(s, Lattice.right s), ?_, ?_⟩
  · exact List.mem_flatMap.2 ⟨s, List.mem_finRange s, List.mem_cons_self ..⟩
  · intro h
    have := congrArg Fin.val h
    simp only [s, Lattice.right, Lattice.site, Nat.zero_div, Nat.zero_mod, Nat.zero_mul,
      Nat.zero_add] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    exact absurd this (by decide)

/-- **正方格子でのシミュレーション**：`L ≥ 2`、`0 < x < 1` なら、実装が動かす連鎖は
Boltzmann 分布について詳細釣り合いを満たし、エルゴード的である。 -/
theorem square_simulation (L : Nat) (hL : 2 ≤ L) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1) :
    Chain.DetailedBalance (boltzmann (Lattice.square L) x)
        (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D) ∧
      Chain.Ergodic (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D) :=
  ⟨simulation_detailed_balance _ x hx0 (Rat.le_of_lt hx1),
    simulation_ergodic _ x hx0 hx1 (square_has_bond hL)⟩

/-- **正方格子でのシミュレーションの収束**：`L ≥ 2`、`0 < x < 1` なら、実装が動かす連鎖は
任意の初期分布から Boltzmann 分布へ幾何的に収束する。 -/
theorem square_simulation_converges (L : Nat) (hL : 2 ≤ L) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1) :
    Chain.GeometricConvergence (boltzmann (Lattice.square L) x)
        (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D) ∧
      Chain.Converges (boltzmann (Lattice.square L) x)
        (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D) :=
  ⟨simulation_geometric _ x hx0 hx1 (square_has_bond hL),
    simulation_converges _ x hx0 hx1 (square_has_bond hL)⟩

/-! ## 乱数の棄却法 -/

theorem countP_mod_range (m k : Nat) (hk : k < m) :
    ∀ q : Nat, (List.range (m * q)).countP (fun j => j % m == k) = q
  | 0 => by simp
  | q + 1 => by
    rw [Nat.mul_succ, List.range_add, List.countP_append, countP_mod_range m k hk q, List.countP_map]
    have : (List.range m).countP ((fun j => j % m == k) ∘ fun j => m * q + j) =
        (List.range m).countP (fun j => j == k) := by
      apply List.countP_congr
      intro j hj
      have hj' : j < m := List.mem_range.1 hj
      simp only [Function.comp, Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
    rw [this, ← List.count_eq_countP, List.count_range]
    simp [hk]

/-- **棄却法の一様性**：`[0, M)` の語のうち採用されるもの `w ∈ [M % m, M)` の中で、
出力 `(w - M % m) % m` が `k ∈ [0, m)` になるものはちょうど `⌊M / m⌋` 個。
したがって源が一様なら、出力は `[0, m)` 上で厳密に一様。 -/
theorem rejection_exact (M m k : Nat) (hk : k < m) :
    (List.range' (M % m) (M - M % m)).countP (fun w => (w - M % m) % m == k) = M / m := by
  rw [List.range'_eq_map_range, List.countP_map]
  have e : M - M % m = m * (M / m) := by have := Nat.mod_add_div M m; omega
  rw [e]
  have : (List.range (m * (M / m))).countP ((fun w => (w - M % m) % m == k) ∘ fun j => M % m + j) =
      (List.range (m * (M / m))).countP (fun j => j % m == k) := by
    apply List.countP_congr
    intro j _
    simp only [Function.comp, Nat.add_sub_cancel_left]
  rw [this, countP_mod_range m k hk]

end LeanIsing.Proofs
