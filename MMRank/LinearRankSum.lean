import MMRank.RankFactorization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Set.Card

/-! # Ранг конечной суммы линейных отображений и матриц -/

namespace MMRank
open Module
variable {K V W I : Type*} [DivisionRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Субаддитивность ранга конечной суммы; конечномерны только образы. -/
theorem finrank_range_sum_le [Fintype I] (f : I → V →ₗ[K] W)
    [∀ i, FiniteDimensional K (f i).range] :
    finrank K (LinearMap.range (∑ i, f i)) ≤ ∑ i, finrank K (f i).range := by
  let a : V →ₗ[K] (∀ i, (f i).range) := LinearMap.pi (fun i ↦ (f i).rangeRestrict)
  let b : (∀ i, (f i).range) →ₗ[K] W :=
    { toFun := fun x ↦ ∑ i, (x i).val
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  have he : b.comp a = ∑ i, f i := by ext x; simp [a, b, LinearMap.sum_apply]
  have hh := finrank_range_le_of_factorization a b
  rw [he, Module.finrank_pi_fintype] at hh
  exact hh

/-- Ранг суммы матриц не больше суммы рангов, для любых конечных размеров. -/
theorem matrix_rank_sum_le {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    [Fintype I] (A : I → Matrix m n F) :
    (∑ i, A i).rank ≤ ∑ i, (A i).rank := by
  classical
  have h := finrank_range_sum_le (fun i ↦ (A i).mulVecLin)
  have he : (∑ i, A i).mulVecLin = ∑ i, (A i).mulVecLin := by
    ext x j
    simp
  change finrank F (∑ i, A i).mulVecLin.range ≤ _
  rw [he]
  exact h

section Weighted
open Matrix
open scoped BigOperators Classical
variable {F M N : Type*} [Field F] [Fintype M] [Fintype N] [Fintype I]

/-- Нулевые веса исключаются из стоимости суммы.
-/
theorem matrix_rank_weighted_sum_le (A : I → Matrix M N F) (a : I → F) (r : ℕ)
    (hr : ∀ i, (A i).rank ≤ r) :
    (∑ i, a i • A i).rank ≤ {i | a i ≠ 0}.ncard * r := by
  classical
  have h := matrix_rank_sum_le (fun i ↦ a i • A i)
  have hs : (∑ i, (a i • A i).rank) ≤ ∑ i, if a i ≠ 0 then r else 0 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases ha : a i = 0
    · simp [ha]
    · rw [ite_eq_left ha, rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ha)]
      exact hr i
  have he : (∑ i, if a i ≠ 0 then r else 0) = {i | a i ≠ 0}.ncard * r := by
    rw [Finset.sum_ite]
    simp [Set.ncard_eq_toFinset_card']
  exact h.trans (hs.trans_eq he)

end Weighted

end MMRank
