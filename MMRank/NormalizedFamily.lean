import MMRank.AnnihilatorCapacity

/-! # Нормировка совместимых семейств по обратимому значению -/

namespace MMRank

open Module

section Ring
variable {R X V W Y : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Y] [Module R Y]

/-- Нормировка по изоморфизму e:V≃W. На строках это e⁻¹C(x);
в порядке LinearMap.comp это C(x)∘e⁻¹, эндоморфизм W. -/
noncomputable def normalizeLinearFamily (C : X →ₗ[R] (V →ₗ[R] W)) (e : V ≃ₗ[R] W) :
    X →ₗ[R] (W →ₗ[R] W) :=
  (e.arrowCongr (LinearEquiv.refl R W)).toLinearMap.comp C

@[simp] theorem normalizeLinearFamily_apply (C : X →ₗ[R] (V →ₗ[R] W))
    (e : V ≃ₗ[R] W) (x : X) (w : W) :
    normalizeLinearFamily C e x w = C x (e.symm w) := rfl

end Ring

section Field
variable {K X V W Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

end Field
end MMRank
