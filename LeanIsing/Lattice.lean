import LeanIsing.Spec

/-!
# 格子

* `square L`：`L × L` の正方格子（周期境界条件）。シミュレーションの本命。
* `ring n`：`n` サイトの 1 次元の環（周期境界条件）。テスト用の小さな系。

どちらも `Graph` の一例にすぎず、証明（`Proofs/`）は任意の `Graph` について成り立つ。
-/

namespace LeanIsing.Lattice

theorem row_lt {L r c : Nat} (hr : r < L) (hc : c < L) : r * L + c < L * L :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hc (r * L))
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L hr)

/-- 格子点 `(r, c)` のサイト番号 `r * L + c`。 -/
def site (L r c : Nat) (hr : r < L) (hc : c < L) : Fin (L * L) :=
  ⟨r * L + c, row_lt hr hc⟩

theorem pos_of_fin {L : Nat} (s : Fin (L * L)) : 0 < L := by
  cases L with
  | zero => exact absurd s.isLt (Nat.not_lt_zero _)
  | succ L => exact Nat.succ_pos L

theorem div_lt {L : Nat} (s : Fin (L * L)) : s.val / L < L :=
  (Nat.div_lt_iff_lt_mul (pos_of_fin s)).2 s.isLt

theorem mod_lt' {L : Nat} (s : Fin (L * L)) : s.val % L < L :=
  Nat.mod_lt _ (pos_of_fin s)

/-- 右隣（列方向に周期的）。 -/
def right {L : Nat} (s : Fin (L * L)) : Fin (L * L) :=
  site L (s.val / L) ((s.val % L + 1) % L) (div_lt s) (Nat.mod_lt _ (pos_of_fin s))

/-- 下隣（行方向に周期的）。 -/
def down {L : Nat} (s : Fin (L * L)) : Fin (L * L) :=
  site L ((s.val / L + 1) % L) (s.val % L) (Nat.mod_lt _ (pos_of_fin s)) (mod_lt' s)

/-- `L × L` の正方格子（周期境界条件）。各サイトから右と下へ 1 本ずつ、計 `2L²` 本のボンドを張る。
`L ≥ 3` なら各サイトの隣は上下左右の 4 個。 -/
def square (L : Nat) : Graph where
  n := L * L
  bonds := (List.finRange (L * L)).flatMap fun s => [(s, right s), (s, down s)]

/-- `n` サイトの環（周期境界条件）。ボンドは `(i, i + 1 mod n)`。 -/
def ring (n : Nat) : Graph where
  n := n
  bonds := (List.finRange n).map fun i => (i, ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩)

end LeanIsing.Lattice
