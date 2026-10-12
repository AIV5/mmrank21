module

public import MMRank.ProjectiveFrameCoordinates
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FieldSimp
public import MMRank.JointSymmetrizerPairCapacity
public import MMRank.ProportionalBlockFactor
public import Mathlib.LinearAlgebra.Matrix.Basis

@[expose] public section

/-! # Матричная реализация двух независимых базисов репера -/
namespace MMRank
open Matrix Module
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Обратимая матрица с базисными векторами в строках. -/
noncomputable def basisRowUnit (b : Basis n K (n → K)) : (Matrix n n K)ˣ where
  val := ((Pi.basisFun K n).toMatrix b).transpose
  inv := (b.toMatrix (Pi.basisFun K n)).transpose
  val_inv := by rw [← transpose_mul, Basis.toMatrix_mul_toMatrix_flip]; simp
  inv_val := by rw [← transpose_mul, Basis.toMatrix_mul_toMatrix_flip]; simp

@[simp] theorem basisRowUnit_apply (b : Basis n K (n → K)) (i j : n) :
    (basisRowUnit b : Matrix n n K) i j = b i j := by
  simp [basisRowUnit, Basis.toMatrix_apply]

/-- Координатная строка переходит в физический вектор базисной матрицей. -/
theorem basis_coordinates_vecMul (b : Basis n K (n → K)) (x : n → K) :
    (fun i ↦ b.repr x i) ᵥ* (basisRowUnit b : Matrix n n K) = x := by
  have hh := b.sum_repr x
  ext j
  simpa [vecMul, dotProduct, Finset.sum_apply] using congrFun hh j

/-- Контрагредиентное произведение двух базисных матриц переносит
простой координатный тест в исходный физический тест. -/
theorem basis_frame_test (b c : Basis n K (n → K)) (x y : n → K) :
    (basisRowUnit b : Matrix n n K)ᵀ * vecMulVec (fun i ↦ b.repr x i) (fun i ↦ c.repr y i) *
      (basisRowUnit c : Matrix n n K) = vecMulVec x y := by
  rw [mul_vecMulVec, vecMulVec_mul, basis_coordinates_vecMul]
  have hh : (basisRowUnit b : Matrix n n K)ᵀ *ᵥ (fun i ↦ b.repr x i) = x := by
    simpa only [mulVec_transpose] using basis_coordinates_vecMul b x
  rw [hh]

/-- Диагональная матричная единица переносится в пару базисных направлений. -/
theorem basis_frame_single (b c : Basis n K (n → K)) (i : n) :
    (basisRowUnit b : Matrix n n K)ᵀ * single i i 1 * (basisRowUnit c : Matrix n n K) =
      vecMulVec (b i) (c i) := by
  have hh := basis_frame_test b c (b i) (c i)
  have he : vecMulVec (fun j ↦ b.repr (b i) j) (fun j ↦ c.repr (c i) j) = single i i 1 := by
    ext j k
    by_cases hj : i = j <;> by_cases hk : i = k <;>
      simp [vecMulVec, single, Finsupp.single_apply, hj, hk]
  rwa [he] at hh

end MMRank
