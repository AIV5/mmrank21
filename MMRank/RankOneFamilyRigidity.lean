import MMRank.CommonLineRigidity

/-! # Ранг один в инъективном трёхпараметрическом семействе

Локальные ограничения на образы семейств на ядрах склеиваются в общий образ.
Все результаты действуют над произвольным полем.
-/

namespace MMRank

open Module

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

/-- Различные плоскости в трёхмерном пространстве порождают всё пространство
и пересекаются по прямой. -/
theorem planes_sup_eq_top_and_finrank_inf (hV : finrank K V = 3)
    (H H' : Submodule K V) (hH : finrank K H = 2) (hH' : finrank K H' = 2)
    (hne : H ≠ H') : H ⊔ H' = ⊤ ∧ finrank K ↥(H ⊓ H') = 1 := by
  have hsup : H ⊔ H' = ⊤ := by
    by_contra ht
    have hd := Submodule.finrank_lt ht
    have hleft : H = H ⊔ H' := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have hright : H' = H ⊔ H' := Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
    exact hne (hleft.trans hright.symm)
  refine ⟨hsup, ?_⟩
  have hd := Submodule.finrank_sup_add_finrank_inf_eq H H'
  rw [hsup, finrank_top, hV, hH, hH'] at hd
  omega

end MMRank
