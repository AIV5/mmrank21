import MMRank.InvariantPointDecomposition
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Инвариантное координатное пространство порождено точечными словами -/
namespace MMRank
variable {K I : Type*} [Field K] [Finite I]

/-- Для включения инвариантного пространства достаточно проверить его
точечные слова. Никакая одномерность сечений или бесконечность поля не нужна. -/
theorem invariant_le_of_pointWords (M N L : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M) (hmul : M * N = N)
    (h : ∀ w ∈ N, IsPointWord M w → w ∈ L) : N ≤ L := by
  rw [← (coordinateComponents_direct N).2]
  apply iSup_le
  intro c w hw
  by_cases hz : w = 0
  · simpa only [hz] using L.zero_mem
  · exact h w (mem_coordinateSection.mp hw).1
      (isPointWord_of_mem_invariant_component M N h1 hmul c w hw hz)

/-- Точная оболочка точечных слов, в том числе при N=0. -/
theorem invariant_eq_span_pointWords (M N : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M) (hmul : M * N = N) :
    N = Submodule.span K {w | w ∈ N ∧ IsPointWord M w} := by
  apply le_antisymm
  · exact invariant_le_of_pointWords M N _ h1 hmul
      (fun w hw hp ↦ Submodule.subset_span ⟨hw, hp⟩)
  · exact Submodule.span_le.mpr (fun _ hw ↦ hw.1)

/-- Из инвариантного пространства выбираются n независимых точечных слов.
Поле произвольно, одномерность компонент не нужна. -/
theorem exists_linearIndependent_pointWords_of_invariant
    (M N : Submodule K (I → K)) (h1 : (1 : I → K) ∈ M) (hmul : M * N = N)
    (n : ℕ) (hn : n ≤ Module.finrank K N) :
    ∃ w : Fin n → I → K, (∀ j, w j ∈ N ∧ IsPointWord M (w j)) ∧
      LinearIndependent K w := by
  have hh := Submodule.exists_fun_fin_finrank_span_eq K {w | w ∈ N ∧ IsPointWord M w}
  rw [← invariant_eq_span_pointWords M N h1 hmul] at hh
  obtain ⟨w, hw, _, hi⟩ := hh
  exact ⟨w ∘ Fin.castLE hn, fun j ↦ hw _, hi.comp _ (Fin.castLE_injective hn)⟩

end MMRank
