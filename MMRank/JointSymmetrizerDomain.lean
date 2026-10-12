module

public import MMRank.JointSymmetrizers

@[expose] public section

/-! # Независимые замены параметров и пространства строк -/

namespace MMRank
variable {R U U' S S' Z W : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup U'] [Module R U']
  [AddCommGroup S] [Module R S] [AddCommGroup S'] [Module R S']
  [AddCommGroup Z] [Module R Z] [AddCommGroup W] [Module R W]

def domainCoordinateFamily (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (a : U' ≃ₗ[R] U) (b : S' ≃ₗ[R] S) : Z →ₗ[R] U' →ₗ[R] S' →ₗ[R] W where
  toFun z := ((B z).compl₂ b.toLinearMap).comp a.toLinearMap
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp] theorem domainCoordinateFamily_apply (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (a : U' ≃ₗ[R] U) (b : S' ≃ₗ[R] S) (z : Z) (u : U') (s : S') :
    domainCoordinateFamily B a b z u s = B z (a u) (b s) := rfl

theorem jointSymmetrizer_domainCoordinateFamily
    (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W) (a : U' ≃ₗ[R] U) (b : S' ≃ₗ[R] S) :
    jointSymmetrizer (domainCoordinateFamily B a b) =
      (jointSymmetrizer B).map (a.symm.arrowCongr b.symm).toLinearMap := by
  ext M
  constructor
  · intro h
    refine ⟨a.arrowCongr b M, ?_, ?_⟩
    · intro z u v
      have hh := h z (a.symm u) (a.symm v)
      simpa [domainCoordinateFamily_apply, LinearEquiv.arrowCongr_apply] using hh
    · ext u; simp [LinearEquiv.arrowCongr_apply]
  · rintro ⟨N, hN, rfl⟩ z u v
    simpa [LinearEquiv.arrowCongr_apply] using hN z (a u) (a v)

theorem domainCoordinateFamily_nz (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (a : U' ≃ₗ[R] U) (b : S' ≃ₗ[R] S)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0) :
    ∀ z u, domainCoordinateFamily B a b z u = 0 → z = 0 ∨ u = 0 := by
  intro z u h
  have hz : B z (a u) = 0 := by
    ext s
    have hh := DFunLike.congr_fun h (b.symm s)
    simpa using hh
  simpa using hnz z (a u) hz

end MMRank
