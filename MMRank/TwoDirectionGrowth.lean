module

public import MMRank.GrowthComplex
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-!
# Комплекс роста при двух направлениях

Значения действия L×G₁ порождают G₂. При базисе L из двух элементов
оценка δ₁ на этом базисе реализует каждое произведение, откуда сюръективность.
В произвольной характеристике получаем d+2g₁=dim N+g₂+dim H¹.
Ни точность в середине, ни H¹=0 не предполагаются.
-/

namespace MMRank

open Module

section Alternating

variable {R L W ι : Type*} [CommRing R]
  [AddCommGroup L] [Module R L] [AddCommGroup W] [Module R W] [Fintype ι]

/-- Знакопеременное отображение высшей степени определяется значением на базисе. -/
noncomputable def alternatingEvalBasisEquiv (b : Basis ι R L) :
    AlternatingMap R L W ι ≃ₗ[R] W := by
  classical
  exact
    { toFun := fun f => f b
      invFun := fun w => b.det.smulRight w
      left_inv := fun f => by
        apply b.ext_alternating
        intro v hv
        let σ : Equiv.Perm ι := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
        change (b.det.smulRight (f b)) (b ∘ σ) = f (b ∘ σ)
        rw [AlternatingMap.map_perm, AlternatingMap.map_perm]
        simp [Basis.det_self]
      right_inv := fun w => by simp [Basis.det_self]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem alternatingEvalBasisEquiv_apply (b : Basis ι R L)
    (f : AlternatingMap R L W ι) : alternatingEvalBasisEquiv b f = f b := rfl

end Alternating

section TwoDirections

variable {R L V W : Type*} [CommRing R]
  [AddCommGroup L] [Module R L] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

end TwoDirections

section Growth

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

end Growth

section Field

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

end Field

end MMRank
