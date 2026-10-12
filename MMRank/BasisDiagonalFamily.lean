module

public import MMRank.JointSymmetrizers
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-! # Диагональное семейство из базисных простых симметризаторов -/
namespace MMRank
open Module
variable {R U S W Z J : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup S] [Module R S]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]

/-- Диагональное отображение второго семейства в паре согласованных базисов. -/
noncomputable def basisDiagonalFactor (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (b : Basis J R U) (c : Basis J R S) (j : J) : Z →ₗ[R] W where
  toFun z := B z (b j) (c j)
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- Простой симметризатор coord_j⊗c_j вынуждает точную j-ю строку.
Конечномерность и поле не нужны. -/
theorem apply_basis_eq_smul_diagonalFactor
    (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W) (b : Basis J R U) (c : Basis J R S)
    (h : ∀ j, (b.coord j).smulRight (c j) ∈ jointSymmetrizer B)
    (z : Z) (u : U) (j : J) :
    B z u (c j) = b.repr u j • basisDiagonalFactor B b c j z := by
  have hh := h j z u (b j)
  simpa [basisDiagonalFactor, Basis.coord_apply] using hh

variable {K : Type*} [Field K] [Module K U] [Module K S] [Module K W] [Module K Z]

/-- NZ всего билинейного семейства делает каждый диагональный фактор инъективным. -/
theorem basisDiagonalFactor_injective
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] W) (b : Basis J K U) (c : Basis J K S)
    (h : ∀ j, (b.coord j).smulRight (c j) ∈ jointSymmetrizer B)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0) (j : J) :
    Function.Injective (basisDiagonalFactor B b c j) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hh : B z (b j) = 0 := by
    apply c.ext
    intro k
    rw [apply_basis_eq_smul_diagonalFactor B b c h]
    by_cases he : j = k
    · subst k; simp [hz]
    · simp [he]
  exact (hnz z (b j) hh).resolve_right (b.ne_zero j)

end MMRank
