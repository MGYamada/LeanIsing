import Lake
open Lake DSL

/-!
# LeanIsing

Lean 4 だけで書いた 2 次元 Ising 模型の Metropolis シミュレーションと、
その詳細釣り合い・エルゴード性の証明。外部依存はなし（Lean core だけを使う。Mathlib も使わない）。
-/

package leanising where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- 仕様・乱数・格子・実行系・シミュレーション本体。 -/
@[default_target]
lean_lib LeanIsing

/-- 詳細釣り合い・エルゴード性・実装の厳密性の証明と、公理監査 `Proofs.Audit`。 -/
@[default_target]
lean_lib Proofs where
  globs := #[.andSubmodules `Proofs]

/-- 実行系の単体テスト（ビルド時に評価する `#guard`）。 -/
@[default_target]
lean_lib Tests where
  globs := #[.andSubmodules `Tests]

/-- シミュレーションの実行ファイル。 -/
@[default_target]
lean_exe ising where
  root := `Main
