import MMRank.JointSymmetrizerPairCapacity

/-! # Ранговая нормальная форма с явными единицами кольца матриц

Перестановки работают над коммутативным полукольцом; нормировка ранга два
использует общую теорему mathlib над исходным полем.
-/

set_option backward.isDefEq.respectTransparency false

namespace MMRank
open Matrix
section Permutation
variable {K n : Type*} [CommSemiring K] [Fintype n] [DecidableEq n]

/-- Единица кольца матриц, переставляющая строки по e. -/
def matrixPermutationUnit (e : n ≃ n) : (Matrix n n K)ˣ where
  val := (1 : Matrix n n K).submatrix e id
  inv := (1 : Matrix n n K).submatrix id e
  val_inv := by
    simpa [submatrix_submatrix] using
      (one_submatrix_mul (α := K) e (Equiv.refl n) ((1 : Matrix n n K).submatrix id e))
  inv_val := by
    rw [mul_submatrix_one e id]
    simp [submatrix_submatrix]

theorem matrixPermutationUnit_mul (e : n ≃ n) (M : Matrix n n K) :
    (↑(matrixPermutationUnit (K := K) e) : Matrix n n K) * M *
      (↑(matrixPermutationUnit (K := K) e)⁻¹ : Matrix n n K) =
      M.submatrix e e := by
  change (1 : Matrix n n K).submatrix e id * M * (1 : Matrix n n K).submatrix id e = _
  have he : (1 : Matrix n n K).submatrix e id * M = M.submatrix e id := by
    simpa using (one_submatrix_mul (α := K) e (Equiv.refl n) M)
  rw [he]
  simpa [submatrix_submatrix] using
    (mul_submatrix_one (α := K) (Equiv.refl n) e (M.submatrix e id))

end Permutation

variable {K : Type*} [Field K]

end MMRank
