import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace MMRank
open Module

/-- Ограничение отображения на вложенное пространство оплачивает потерю ранга
не большей коразмерности этого пространства. -/
theorem finrank_range_add_le_of_injective
    {K X Y T : Type*} [DivisionRing K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y]
    [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (f : X →ₗ[K] Y) (g : T →ₗ[K] X) (hg : Function.Injective g) :
    finrank K f.range + finrank K T ≤ finrank K X + finrank K (f.comp g).range := by
  have hk : ((f.comp g).ker).map g ≤ f.ker := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht
  have hd := Submodule.finrank_mono hk
  rw [← (Submodule.equivMapOfInjective g hg (f.comp g).ker).finrank_eq] at hd
  have hf := f.finrank_range_add_finrank_ker
  have ht := (f.comp g).finrank_range_add_finrank_ker
  omega

/-- Подпространство ядра внутри E оплачивается падением ранга образа E. -/
theorem finrank_map_add_le_of_le_ker
    {K X Y : Type*} [DivisionRing K]
    [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (f : X →ₗ[K] Y) (E L : Submodule K X) [FiniteDimensional K E]
    (hLE : L ≤ E) (hL : L ≤ f.ker) :
    finrank K (E.map f) + finrank K L ≤ finrank K E := by
  let g : L →ₗ[K] E := Submodule.inclusion hLE
  have hz : (f.domRestrict E).comp g = 0 := by
    ext x
    exact hL x.property
  let : FiniteDimensional K L := Submodule.finiteDimensional_of_le hLE
  have hh := finrank_range_add_le_of_injective (f.domRestrict E) g
    (Submodule.inclusion_injective hLE)
  rw [hz, LinearMap.range_zero, finrank_bot, add_zero, LinearMap.range_domRestrict] at hh
  exact hh

end MMRank
