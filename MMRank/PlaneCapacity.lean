module

public import MMRank.SupportedTestBudgets
public import MMRank.SupportedPartialProduct

@[expose] public section

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Вместимость любой фиксированной плоскости при длине≤20.
Точечные слова допускаются. Нужна только нормировка на одной гиперплоскости,
без общности направления, NZ, бесконечности и алгебраической замкнутости. -/
theorem plane_capacity (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (F : Submodule K (P → K)) (hF : finrank K F = 2) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F) :
    finrank K (alg.toCoefficients.supportedTests G) ≤ 2 ∧
      G.ncard ≤ finrank K (alg.toCoefficients.supportedTests G) + 5 ∧ G.ncard ≤ 7 := by
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  have he := alg.supportedTests_exterior_budget F G hG (by omega)
  have hi := alg.supportedTests_internal_budget_of_hyperplane G η hη h1
  have hc := alg.supportedTests_capacity F G hG
  rw [hq, hs, hF] at he
  rw [hq] at hi
  rw [hF] at hc
  have hm : G.ncard ≤ finrank K (alg.toCoefficients.supportedTests G) + 5 := by omega
  have him : finrank K (alg.toCoefficients.supportedTestImage G) ≤ 2 := by omega
  have hdim : finrank K (alg.toCoefficients.supportedTests G) ≤ 2 := by
    by_contra hn
    have him2 : finrank K (alg.toCoefficients.supportedTestImage G) = 2 := by omega
    have hh := alg.supportedTests_dimension_lower F G hG hF him2 (by omega)
    rw [hq] at hh
    omega
  exact ⟨hdim, hm, by omega⟩

/-- Та же граница для фактического внутреннего сечения imγ. -/
theorem plane_coordinateSection_capacity (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (F : Submodule K (P → K)) (hF : finrank K F = 2) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F) :
    finrank K (coordinateSection K alg.toCoefficients.gamma.range G) ≤ 2 ∧ G.ncard ≤ 7 := by
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hd, _, hm⟩ := alg.plane_capacity hp hq hs hl η hη h1 F hF G hG
  rw [(alg.supportedTestsEquiv G).finrank_eq] at hd
  exact ⟨hd, hm⟩

end MMRank.ExactAlgorithm
