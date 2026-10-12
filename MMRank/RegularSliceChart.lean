module

public import MMRank.SubspaceMatrixChart
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Bilinear

@[expose] public section

/-! # Регулярный тест в координатах двух совместных носителей

Двусторонняя модель сохраняет
ранги тестов, а её левый множитель одновременно служит координатами U.
-/
namespace MMRank
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S]

/-- При фиксированных носителях тестов координаты сохраняют ранги и
совместимы с левым действием произвольного оператора. -/
theorem exists_two_sided_slice_chart
    (T : Submodule K (Matrix P S K)) (F : Submodule K (P → K))
    (R : Submodule K (S → K)) (p s : ℕ)
    (hF : finrank K F = p) (hR : finrank K R = s)
    (hcols : ∀ C ∈ T, C.transpose ∈ matricesInto F)
    (hrows : ∀ C ∈ T, C ∈ matricesInto R) :
    ∃ (E : Matrix P (Fin p) K) (L : Matrix (Fin p) P K)
      (D : Matrix S (Fin s) K)
      (j : Matrix (Fin p) (Fin s) K →ₗ[K] Matrix P S K),
      L * E = 1 ∧
      (∀ A : Matrix P Q K, A.transpose ∈ matricesInto F → E * (L * A) = A) ∧
      Function.Injective j ∧ T ≤ j.range ∧
      (∀ C, (j C).rank = C.rank) ∧
      (∀ C, L * j C * D = C) ∧
      (∀ H : Matrix (Fin p) (Fin p) K, ∀ C, L * j (H * C) = H * (L * j C)) := by
  obtain ⟨BF, DF, hFD, _, hFr⟩ := exists_subspace_matrix_chart F p hF
  let E := BF.transpose
  let L := DF.transpose
  have hLE : L * E = 1 := by
    change DF.transpose * BF.transpose = 1
    rw [← transpose_mul, hFD, transpose_one]
  have hretQ (A : Matrix P Q K) (hA : A.transpose ∈ matricesInto F) : E * (L * A) = A := by
    simpa only [transpose_mul, transpose_transpose] using
      congrArg Matrix.transpose (mul_retraction_of_rows F BF DF hFr A.transpose hA)
  have hretS (A : Matrix P S K) (hA : A.transpose ∈ matricesInto F) : E * (L * A) = A := by
    simpa only [transpose_mul, transpose_transpose] using
      congrArg Matrix.transpose (mul_retraction_of_rows F BF DF hFr A.transpose hA)
  obtain ⟨B, D, hBD, _, hRret⟩ := exists_subspace_matrix_chart R s hR
  let j : Matrix (Fin p) (Fin s) K →ₗ[K] Matrix P S K :=
    (mulRightLinearMap P K B).comp (mulLeftLinearMap (Fin s) K E)
  have hj (C : Matrix (Fin p) (Fin s) K) : L * j C * D = C := by
    change L * (E * C * B) * D = C
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc L E, hLE, Matrix.one_mul,
      hBD, Matrix.mul_one]
  refine ⟨E, L, D, j, hLE, hretQ, ?_, ?_, ?_, hj, ?_⟩
  · intro C D h
    rw [← hj C, ← hj D, h]
  · intro C hC
    refine ⟨L * C * D, ?_⟩
    change E * (L * C * D) * B = C
    rw [← Matrix.mul_assoc E, hretS C (hcols C hC)]
    exact mul_retraction_of_rows R B D hRret C (hrows C hC)
  · intro C
    apply le_antisymm
    · change (E * C * B).rank ≤ C.rank
      exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    · calc
        C.rank = (L * j C * D).rank := congrArg Matrix.rank (hj C).symm
        _ ≤ (j C).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · intro H C
    change L * (E * (H * C) * B) = H * (L * (E * C * B))
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc L E, hLE, Matrix.one_mul]

end MMRank
