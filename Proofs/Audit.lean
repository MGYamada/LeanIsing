import Proofs.Theorems
import Lean

/-!
# 主張と公理の監査

`lake build` のたびに次を検査し、1 つでも違反があればビルドを失敗させる。

1. 主定理の主張が、ここに書いた式と（reducible な展開だけで）一致する。
   定理の名前と中身がすり替わっていないことを、仕様（`LeanIsing.Spec`）の言葉だけで確認する。
2. 主定理が依存する公理が、Lean の標準公理 `propext`・`Classical.choice`・`Quot.sound` だけである。
   `sorryAx`（証明の穴）も、`native_decide` が使う `Lean.ofReduceBool` / `Lean.trustCompiler` も使っていない。
-/

open Lean Elab Command Meta

namespace LeanIsing.Audit

/-- 定理 `thm` の主張が `stx` を elaborate した式と一致するか確かめる。 -/
def checkStatement (thm : Name) (stx : Term) : CommandElabM Unit := liftTermElabM do
  let some info := (← getEnv).find? thm | throwError "定理 {thm} が見つかりません"
  unless info matches .thmInfo _ do throwError "{thm} は定理ではありません"
  let expected ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  unless ← withReducible (isDefEq info.type expected) do
    throwError "{thm} の主張が期待と異なります:{indentExpr info.type}\n期待:{indentExpr expected}"

/-- 許す公理（Lean の標準公理）。 -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- 定理 `thm` が標準公理以外に依存していないことを確かめる。 -/
def checkAxioms (thm : Name) : CommandElabM Unit := do
  let axs ← collectAxioms thm
  let bad := axs.filter (fun a => !allowedAxioms.contains a)
  unless bad.isEmpty do
    throwError "{thm} が標準公理以外に依存しています: {bad}"

run_cmd do
  let checks : List (Name × Term) := [
    (``LeanIsing.Proofs.metropolis_stochastic,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → 0 < G.n →
        LeanIsing.Chain.Stochastic (LeanIsing.kernel G x))),
    (``LeanIsing.Proofs.metropolis_detailed_balance,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x →
        LeanIsing.Chain.DetailedBalance (LeanIsing.boltzmann G x) (LeanIsing.kernel G x))),
    (``LeanIsing.Proofs.metropolis_stationary,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → 0 < G.n →
        LeanIsing.Chain.Stationary (LeanIsing.boltzmann G x) (LeanIsing.kernel G x))),
    (``LeanIsing.Proofs.metropolis_irreducible,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x →
        LeanIsing.Chain.Irreducible (LeanIsing.kernel G x))),
    (``LeanIsing.Proofs.metropolis_ergodic,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → x < 1 → (∃ b ∈ G.bonds, b.1 ≠ b.2) →
        LeanIsing.Chain.Ergodic (LeanIsing.kernel G x))),
    (``LeanIsing.Proofs.simulation_exact,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → x ≤ 1 →
        LeanIsing.Engine.inducedKernel G x (LeanIsing.Engine.Sim.make G x).D = LeanIsing.kernel G x)),
    (``LeanIsing.Proofs.simulation_detailed_balance,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → x ≤ 1 →
        LeanIsing.Chain.DetailedBalance (LeanIsing.boltzmann G x)
          (LeanIsing.Engine.inducedKernel G x (LeanIsing.Engine.Sim.make G x).D))),
    (``LeanIsing.Proofs.simulation_ergodic,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → x < 1 → (∃ b ∈ G.bonds, b.1 ≠ b.2) →
        LeanIsing.Chain.Ergodic
          (LeanIsing.Engine.inducedKernel G x (LeanIsing.Engine.Sim.make G x).D))),
    (``LeanIsing.Proofs.square_simulation,
      ← `(∀ (L : Nat), 2 ≤ L → ∀ (x : Rat), 0 < x → x < 1 →
        LeanIsing.Chain.DetailedBalance (LeanIsing.boltzmann (LeanIsing.Lattice.square L) x)
            (LeanIsing.Engine.inducedKernel (LeanIsing.Lattice.square L) x
              (LeanIsing.Engine.Sim.make (LeanIsing.Lattice.square L) x).D) ∧
          LeanIsing.Chain.Ergodic (LeanIsing.Engine.inducedKernel (LeanIsing.Lattice.square L) x
              (LeanIsing.Engine.Sim.make (LeanIsing.Lattice.square L) x).D))),
    (``LeanIsing.Proofs.metropolis_geometric,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → x < 1 → (∃ b ∈ G.bonds, b.1 ≠ b.2) →
        LeanIsing.Chain.GeometricConvergence (LeanIsing.boltzmann G x) (LeanIsing.kernel G x))),
    (``LeanIsing.Proofs.metropolis_converges,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → x < 1 → (∃ b ∈ G.bonds, b.1 ≠ b.2) →
        LeanIsing.Chain.Converges (LeanIsing.boltzmann G x) (LeanIsing.kernel G x))),
    (``LeanIsing.Proofs.simulation_converges,
      ← `(∀ (G : LeanIsing.Graph) (x : Rat), 0 < x → x < 1 → (∃ b ∈ G.bonds, b.1 ≠ b.2) →
        LeanIsing.Chain.Converges (LeanIsing.boltzmann G x)
          (LeanIsing.Engine.inducedKernel G x (LeanIsing.Engine.Sim.make G x).D))),
    (``LeanIsing.Proofs.square_simulation_converges,
      ← `(∀ (L : Nat), 2 ≤ L → ∀ (x : Rat), 0 < x → x < 1 →
        LeanIsing.Chain.GeometricConvergence (LeanIsing.boltzmann (LeanIsing.Lattice.square L) x)
            (LeanIsing.Engine.inducedKernel (LeanIsing.Lattice.square L) x
              (LeanIsing.Engine.Sim.make (LeanIsing.Lattice.square L) x).D) ∧
          LeanIsing.Chain.Converges (LeanIsing.boltzmann (LeanIsing.Lattice.square L) x)
            (LeanIsing.Engine.inducedKernel (LeanIsing.Lattice.square L) x
              (LeanIsing.Engine.Sim.make (LeanIsing.Lattice.square L) x).D))),
    (``LeanIsing.Proofs.rejection_exact,
      ← `(∀ (M m k : Nat), k < m →
        (List.range' (M % m) (M - M % m)).countP (fun w => (w - M % m) % m == k) = M / m))
  ]
  for (thm, stx) in checks do
    checkStatement thm stx
  let others := [``LeanIsing.Proofs.simulation_stochastic, ``LeanIsing.Proofs.simulation_stationary,
    ``LeanIsing.Proofs.simulation_irreducible, ``LeanIsing.Proofs.ergodic_from,
    ``LeanIsing.Proofs.irreducible_within, ``LeanIsing.Proofs.Sim.stepPure_fst,
    ``LeanIsing.Proofs.unsat_flip, ``LeanIsing.Proofs.acceptLocal_eq,
    ``LeanIsing.Proofs.simulation_geometric, ``LeanIsing.Proofs.geometric_of_primitive,
    ``LeanIsing.Proofs.converges_of_geometric, ``LeanIsing.Proofs.l1_contract]
  for thm in checks.map (·.1) ++ others do
    checkAxioms thm
  logInfo m!"監査 OK: {checks.length} 個の主定理の主張は期待どおりで、これらと補助定理 {others.length} 個は\
    標準公理（propext, Classical.choice, Quot.sound）だけに依存する（sorry・native_decide なし）。"

end LeanIsing.Audit
