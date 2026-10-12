module

public import MMRank.RankOneMatrixSpaces
public import MMRank.FixedColumnSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import MMRank.ConnectivityCost
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Basis.Prod

@[expose] public section

/-! # Строковые пространства и подъём базисов при фиксированном столбце

Общий прообраз подпространства
инъективного отображения используется для U=p⊗a без выбора отдельного
представителя для каждого вектора. Размеры произвольны.
-/
noncomputable section
namespace MMRank
open Module Submodule Matrix

section Preimage
variable {R E D I : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid D]
  [Module R E] [Module R D]

/-- Инъективное отображение отождествляет полный прообраз A с A,
если A содержится в его образе. -/
def submodulePreimageEquiv (f : D →ₗ[R] E) (hf : Function.Injective f)
    (A : Submodule R E) (hA : A ≤ f.range) : (A.comap f) ≃ₗ[R] A :=
  LinearEquiv.ofBijective
    ((f.domRestrict (A.comap f)).codRestrict A (fun x ↦ x.property)) (by
      constructor
      · intro x y hxy
        exact Subtype.ext (hf (congrArg Subtype.val hxy))
      · intro x
        obtain ⟨y, hy⟩ := hA x.property
        exact ⟨⟨y, by change f y ∈ A; rw [hy]; exact x.property⟩, Subtype.ext hy⟩)

@[simp]
theorem submodulePreimageEquiv_apply (f : D →ₗ[R] E) (hf : Function.Injective f)
    (A : Submodule R E) (hA : A ≤ f.range) (x : A.comap f) :
    (submodulePreimageEquiv f hf A hA x).val = f x.val := rfl

end Preimage

section FixedColumn
variable {K P Q I : Type*} [Field K]

end FixedColumn
end MMRank
