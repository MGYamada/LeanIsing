import LeanIsing.Layered
import Proofs.Model
import Proofs.Exactness

/-!
# 層つき模型の実行系の厳密性

`Layered.inducedKernel M`（実装の 1 ステップ `Layered.step` に、一様なサイト `i` と
`u = k / D`（`D` は受理確率の分母）を与えたときの遷移確率）が、仕様の `M.kernel` に等しいことを示す。

1. 層ごとに `unsat(flip σ i) + disagree = unsat σ + agree`（古典模型の `unsat_flip` をそのまま使う）。
   よって局所比 `Π_l x_l^agree / x_l^disagree` は重みの比 `w(flip σ i) / w(σ)` に等しい。
2. 受理確率 `A` に対して `A · A.den = A.num` は自然数なので、しきい値判定の計数
   `count_threshold` がそのまま使える。
-/

namespace LeanIsing.Proofs

open Layered

variable {n : Nat}

/-- `U' + d = U + a` なら `x^U' / x^U = x^a / x^d`（`x > 0`）。 -/
theorem pow_ratio {x : Rat} (hx : 0 < x) {U U' a d : Nat} (h : U' + d = U + a) :
    x ^ U' / x ^ U = x ^ a / x ^ d := by
  have hU : x ^ U ≠ 0 := Rat.ne_of_gt (Rat.pow_pos hx)
  have hd : x ^ d ≠ 0 := Rat.ne_of_gt (Rat.pow_pos hx)
  have e : x ^ U' * x ^ d = x ^ U * x ^ a := by rw [← pow_add', ← pow_add', h]
  grind

/-- 局所比は重みの比に等しい。 -/
theorem localRatio_eq (σ : Config n) (i : Fin n) :
    ∀ ls : List (List (Fin n × Fin n) × Rat), (∀ l ∈ ls, 0 < l.2) →
      localRatio σ i (ls.map fun l => (nbrsOf l.1 i, l.2)) =
        layerWeight (flip σ i) ls / layerWeight σ ls
  | [], _ => by simp only [List.map_nil, localRatio, layerWeight]; grind
  | l :: rest, h => by
    have hx := h l (List.mem_cons_self ..)
    have hrest : ∀ l' ∈ rest, 0 < l'.2 := fun l' hl' => h l' (List.mem_cons_of_mem l hl')
    have ih := localRatio_eq σ i rest hrest
    simp only [List.map_cons, localRatio, layerWeight]
    rw [ih]
    have hflip : unsatOf l.1 (flip σ i) + Engine.disagree (nbrsOf l.1 i) σ i =
        unsatOf l.1 σ + Engine.agree (nbrsOf l.1 i) σ i := unsat_flip ⟨n, l.1⟩ σ i
    rw [← pow_ratio hx hflip]
    have h1 : l.2 ^ unsatOf l.1 σ ≠ 0 := Rat.ne_of_gt (Rat.pow_pos hx)
    have h2 : layerWeight σ rest ≠ 0 := Rat.ne_of_gt (layerWeight_pos σ rest hrest)
    grind

theorem layered_acceptLocal_eq (M : Model) (hpos : ∀ l ∈ M.layers, 0 < l.2) (σ : Config M.n)
    (i : Fin M.n) : acceptLocal (nbrLayers M i) σ i = acceptW M.weight σ i := by
  unfold acceptLocal acceptW nbrLayers Model.weight
  rw [localRatio_eq σ i M.layers hpos]

/-- サイト `i` を選んだとき、`D = A.den` 通りの `u = k / D` のうち `σ` を `τ` に移すものの割合は `term`。 -/
theorem layered_count_site (M : Model) (hpos : ∀ l ∈ M.layers, 0 < l.2) (σ τ : Config M.n)
    (i : Fin M.n) :
    (((List.range (acceptLocal (nbrLayers M i) σ i).den).countP fun (k : Nat) =>
        decide (step (nbrLayers M i) σ i
          ((k : Rat) / (acceptLocal (nbrLayers M i) σ i).den) = τ) : Nat) : Rat) /
      (acceptLocal (nbrLayers M i) σ i).den = term M.weight σ τ i := by
  have hw : ∀ σ, 0 < M.weight σ := fun σ => layerWeight_pos σ M.layers hpos
  unfold step
  generalize hA : acceptLocal (nbrLayers M i) σ i = A
  have hAeq : A = acceptW M.weight σ i := hA ▸ layered_acceptLocal_eq M hpos σ i
  have h0 : 0 ≤ A := hAeq ▸ Rat.le_of_lt (acceptW_pos hw σ i)
  have h1 : A ≤ 1 := hAeq ▸ acceptW_le_one σ i
  obtain ⟨c, hc, hcD⟩ := mul_nat_of_den_dvd h0 h1 (Nat.dvd_refl A.den)
  rw [count_threshold A.den_pos hc hcD σ τ i]
  have hD : (A.den : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.2 A.den_pos)
  unfold term
  rw [← hAeq]
  rw [Rat.mul_comm]
  exact Rat.mul_div_cancel hD

/-- **層つき模型の実装の厳密性**：因子がすべて正なら、実装の遷移確率は仕様の核に厳密に等しい。 -/
theorem layered_exact (M : Model) (hpos : ∀ l ∈ M.layers, 0 < l.2) :
    Layered.inducedKernel M = M.kernel := by
  funext σ τ
  unfold Layered.inducedKernel
  rw [sum_map_congr (fun i _ => layered_count_site M hpos σ τ i)]
  rfl

theorem Layered.Sim.stepPure_fst' (s : Layered.Sim) (σ : Config s.M.n) (i : Fin s.M.n) (k : Nat) :
    (s.stepPure σ i k).1 =
      step s.tables[i] σ i ((k : Rat) / (acceptLocal s.tables[i] σ i).den) := by
  unfold Layered.Sim.stepPure stepWithFlag step
  simp only [Rat.mkRat_eq_div, Rat.intCast_natCast]
  split <;> rfl

/-- シミュレーションの 1 ステップは、`u = k / D` に対する `step` そのもの。 -/
theorem Layered.Sim.stepPure_fst (M : Model) (σ : Config M.n) (i : Fin M.n) (k : Nat) :
    ((Layered.Sim.make M).stepPure σ i k).1 =
      step (nbrLayers M i) σ i ((k : Rat) / (acceptLocal (nbrLayers M i) σ i).den) := by
  refine (Layered.Sim.stepPure_fst' (Layered.Sim.make M) σ i k).trans ?_
  show step (Vector.ofFn (nbrLayers M))[(i : Nat)] σ i
    ((k : Rat) / (acceptLocal (Vector.ofFn (nbrLayers M))[(i : Nat)] σ i).den) = _
  rw [Vector.getElem_ofFn]

/-! ## 主定理（層つき模型のシミュレーション） -/

theorem layered_simulation_detailed_balance (M : Model) (hM : M.Valid) :
    Chain.DetailedBalance M.boltzmann (Layered.inducedKernel M) := by
  rw [layered_exact M fun l hl => (hM l hl).1]; exact model_detailed_balance M hM

theorem layered_simulation_stationary (M : Model) (hM : M.Valid) (hn : 0 < M.n) :
    Chain.Stationary M.boltzmann (Layered.inducedKernel M) := by
  rw [layered_exact M fun l hl => (hM l hl).1]; exact model_stationary M hM hn

theorem layered_simulation_ergodic (M : Model) (hM : M.Valid) (hF : M.Frustratable) :
    Chain.Ergodic (Layered.inducedKernel M) := by
  rw [layered_exact M fun l hl => (hM l hl).1]; exact model_ergodic M hM hF

theorem layered_simulation_converges (M : Model) (hM : M.Valid) (hF : M.Frustratable) :
    Chain.GeometricConvergence M.boltzmann (Layered.inducedKernel M) ∧
      Chain.Converges M.boltzmann (Layered.inducedKernel M) := by
  rw [layered_exact M fun l hl => (hM l hl).1]
  exact ⟨model_geometric M hM hF, model_converges M hM hF⟩

end LeanIsing.Proofs
