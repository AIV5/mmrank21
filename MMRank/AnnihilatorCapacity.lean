module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

/-! # Вместимость семейств с общим ядром и ограниченным образом -/

namespace MMRank

open Module

/-- Инъективное линейное семейство V→W, зануляющее L и принимающее значения
в F, имеет размерность не более dim(V/L) dim F. -/
theorem finrank_le_annihilator_capacity
    {K V W Z : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z]
    (L : Submodule K V) (F : Submodule K W) [FiniteDimensional K F]
    (f : Z →ₗ[K] (V →ₗ[K] W)) (hf : Function.Injective f)
    (hr : ∀ z, (f z).range ≤ F) (hk : ∀ z, L ≤ (f z).ker) :
    finrank K Z ≤ (finrank K V - finrank K L) * finrank K F := by
  let g : Z →ₗ[K] ((V ⧸ L) →ₗ[K] F) :=
    { toFun := fun z ↦ L.liftQ ((f z).codRestrict F (fun v ↦ hr z ⟨v, rfl⟩))
        (fun v hv ↦ Subtype.ext (hk z hv))
      map_add' := by
        intro a b
        ext x
        change (f (a + b)) x = (f a) x + (f b) x
        simp
      map_smul' := by
        intro a b
        ext x
        change (f (a • b)) x = a • (f b) x
        simp }
  have hi : Function.Injective g := by
    intro a b h
    apply hf
    ext v
    exact congrArg Subtype.val (congrArg (fun t : (V ⧸ L) →ₗ[K] F ↦ t (L.mkQ v)) h)
  have h := LinearMap.finrank_le_finrank_of_injective hi
  rwa [Module.finrank_linearMap, Submodule.finrank_quotient] at h

end MMRank
