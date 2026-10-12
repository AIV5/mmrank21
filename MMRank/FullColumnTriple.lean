import MMRank.PointClassBudget
import MMRank.MinimalTestBasis

namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Ненулевое внутреннее сечение тестов заполняет весь фиксированный
первый класс. Не нужны формат333, минимальная мощность или общность. -/
theorem fixedColumn_span_eq_of_section_ne_bot [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (p : P → K) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p)
    (hδ : coordinateSection K alg.toCoefficients.gamma.range G ≠ ⊥) :
    Submodule.span K (alg.U '' G) = fixedColumnSpace (Q := Q) p := by
  obtain ⟨w, hw, hw0⟩ := (coordinateSection K alg.toCoefficients.gamma.range G).ne_bot_iff.mp hδ
  obtain ⟨C, hC⟩ := (mem_coordinateSection.mp hw).1
  have hsupp : ∀ i ∉ G, alg.toCoefficients.gamma C i = 0 := by
    rw [hC]
    exact (mem_coordinateSection.mp hw).2
  obtain ⟨s, hs⟩ := alg.test_mem_fixedColumnSpace p G hspan C hsupp
  change vecMulVec p s = C at hs
  have hs0 : s ≠ 0 := by
    intro hz
    have he : C = 0 := by
      rw [← hs, hz]
      ext i j
      simp [vecMulVec]
    exact hw0 (by rw [← hC, he, map_zero])
  apply le_antisymm hspan
  apply alg.fixedColumnSpace_le_span_of_gamma_supported G p s hs0
  rwa [hs]

end MMRank.ExactAlgorithm
