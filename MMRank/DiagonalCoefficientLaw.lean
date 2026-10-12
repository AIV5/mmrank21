module

public import MMRank.BasisDiagonalFamily

@[expose] public section

/-! # Полный носитель параметров и нулевое правило диагонального семейства -/
namespace MMRank
open Module
variable {K U S W Z J I : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup S] [Module K S]
  [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

/-- Значение на базисном параметре есть один координатный оператор. -/
theorem diagonalFamily_basis_eq_smulRight
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] W) (b : Basis J K U) (c : Basis J K S)
    (h : ∀ j, (b.coord j).smulRight (c j) ∈ jointSymmetrizer B) (z : Z) (j : J) :
    B z (b j) = (c.coord j).smulRight (basisDiagonalFactor B b c j z) := by
  classical
  apply c.ext
  intro k
  by_cases he : j = k
  · subst k
    simp [apply_basis_eq_smul_diagonalFactor B b c h, Basis.coord_apply]
  · simp [apply_basis_eq_smul_diagonalFactor B b c h, Basis.coord_apply,
      he, Ne.symm he]

end MMRank
