module

public import MMRank.RankFactorization
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Миноры и матрицы с носителем в одной строке или столбце -/

namespace MMRank
open Matrix
variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

omit [Fintype m] in
/-- Все миноры порядка два исчезают при ранге не больше одного. -/
theorem minor_two_eq_zero_of_rank_le_one (A : Matrix m n K) (h : A.rank ≤ 1)
    (i j : m) (k l : n) : A i k * A j l - A i l * A j k = 0 := by
  classical
  let B := A.submatrix ![i, j] ![k, l]
  have hr : B.rank ≤ 1 := (Matrix.rank_submatrix_le A _ _).trans h
  have hd : B.det = 0 := by
    by_contra hh
    have := Matrix.rank_of_det_ne_zero hh
    simp only [Fintype.card_fin] at this
    omega
  rw [Matrix.det_fin_two] at hd
  simpa [B] using hd

end MMRank
