module

public import MMRank.AnnihilatorCapacity

@[expose] public section

/-! # Жёсткость совместимых семейств с общим одномерным образом -/

namespace MMRank

open Module

variable {K V W X T : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X] [AddCommGroup T] [Module K T]

/-- Ненулевое линейное отображение из пространства размерности ≤1 инъективно. -/
theorem linearMap_injective_of_finrank_le_one [FiniteDimensional K V]
    (f : V →ₗ[K] W) (hd : finrank K V ≤ 1) (hf : f ≠ 0) : Function.Injective f := by
  have hr : 0 < finrank K f.range := by
    by_contra! h
    exact hf (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega)))
  have h := f.finrank_range_add_finrank_ker
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

end MMRank
