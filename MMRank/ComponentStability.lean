module

public import MMRank.InvariantPointDecomposition

@[expose] public section

/-! # Одномерные ограничения обеспечивают инвариантность -/
namespace MMRank
open Module
variable {K I : Type*} [Field K] [Finite I]

/-- Если на каждой активной компоненте N пространство множителей имеет
размерность не более одного, то N устойчиво. Не требуется бесконечное поле. -/
theorem mul_eq_of_active_component_restriction_le_one (M N : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M)
    (ha : ∀ c : activeCoordinateComponents N,
      finrank K (coordinateRestriction M c.val).range ≤ 1) : M * N = N := by
  apply le_antisymm
  · apply (mul_le_iff_le_conductor M N N).mpr
    conv_lhs => rw [← (activeCoordinateComponents_direct N).2]
    apply iSup_le
    intro c w hw
    by_cases hz : w = 0
    · simpa only [hz] using (conductor N M).zero_mem
    · exact (isPointWord_of_supported_of_restriction_finrank_le_one M h1 c.val w hz
        (mem_coordinateSection.mp hw).2 (ha c)).mem_conductor (mem_coordinateSection.mp hw).1
  · exact le_mul_of_one_mem M N h1

/-- Для насыщенной пары одномерность всех активных ограничений
означает нулевой рост; формулировка не предполагает N инвариантным. -/
theorem saturated_eq_conductor_of_component_restriction_le_one
    (M N : Submodule K (I → K)) (h1 : (1 : I → K) ∈ M)
    (ha : ∀ c : activeCoordinateComponents (M * conductor N M),
      finrank K (coordinateRestriction M c.val).range ≤ 1) :
    M * conductor N M = conductor N M := by
  have hstable := mul_eq_of_active_component_restriction_le_one M (M * conductor N M) h1 ha
  apply le_antisymm
  · apply (mul_le_iff_le_conductor M _ N).mp
    rw [hstable]
    exact mul_conductor_le M N
  · exact le_mul_of_one_mem M _ h1

/-- Рост насыщенной пары ровно на один требует активной компоненты
с двумерным ограничением множителей. Поле и размерности произвольны. -/
theorem exists_restriction_two_of_growth_one
    (M N : Submodule K (I → K)) (h1 : (1 : I → K) ∈ M)
    (hgrowth : finrank K (M * conductor N M) = finrank K (conductor N M) + 1) :
    ∃ i : I, (∃ w ∈ M * conductor N M, w i ≠ 0) ∧
      finrank K (coordinateRestriction M (coordinateComponent (M * conductor N M) i)).range = 2 := by
  classical
  by_contra! hno
  have he := saturated_eq_conductor_of_component_restriction_le_one M N h1 (by
    intro c
    obtain ⟨i, hi⟩ := c.property.1
    have hactive : ∃ w ∈ M * conductor N M, w i ≠ 0 := by
      change i ∈ {j | ∃ w ∈ M * conductor N M, w j ≠ 0}
      rw [← iUnion_activeCoordinateComponents]
      exact Set.mem_iUnion.mpr ⟨c, hi ▸ mem_coordinateComponent_self _ i⟩
    have hle := saturated_component_restriction_finrank_le M N h1 i
    have hne := hno i hactive
    rw [← hi]
    omega)
  rw [he] at hgrowth
  omega

end MMRank
