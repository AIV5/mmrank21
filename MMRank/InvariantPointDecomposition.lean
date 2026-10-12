module

public import MMRank.ActiveCoordinateComponents
public import MMRank.PointWords

@[expose] public section

/-! # Точечное разложение инвариантного пространства

Нулевой рост, а не наличие одного точечного слова, обеспечивает устойчивость
всего пространства. Размерности и число координат произвольны.
-/

namespace MMRank
open Module
variable {K I : Type*} [Field K] [Finite I]

/-- Любое ненулевое слово сечения инвариантного пространства по его
канонической компоненте является точечным. Бесконечность поля не нужна. -/
theorem isPointWord_of_mem_invariant_component (M N : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M) (hmul : M * N = N)
    (c : Set.range (coordinateComponent N)) (w : I → K)
    (hw : w ∈ coordinateSection K N c.val) (hw0 : w ≠ 0) : IsPointWord M w := by
  have hc : conductor N M = N := by
    apply le_antisymm (conductor_le_of_one_mem N M h1)
    exact (mul_le_iff_le_conductor M N N).mp hmul.le
  obtain ⟨s, i, rfl⟩ := c
  apply isPointWord_of_supported_of_restriction_finrank_le_one M h1 _ w hw0
    (mem_coordinateSection.mp hw).2
  have hh := saturated_component_restriction_finrank_le M N h1 i
  rw [hc, hmul, Nat.sub_self, Nat.zero_add] at hh
  exact hh

end MMRank
