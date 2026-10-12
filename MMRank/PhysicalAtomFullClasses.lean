module

public import MMRank.PhysicalAtomIntersections
public import MMRank.PointTestRecalibration
public import MMRank.SecondConductorIntoFamily

@[expose] public section

/-! # Полные физические классы атома и тесты нового кондуктора -/
namespace MMRank.ExactAlgorithm.PhysicalAtom
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  {alg : ExactAlgorithm K P Q S I}

/-- На любой нормированной гиперплоскости физический атом снова точечный.
Общность гиперплоскости, Infinite K и размер3 не нужны. -/
theorem isPointWord (a : PhysicalAtom alg) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η)) :
    IsPointWord (alg.toCoefficients.alphaOn (coordinateHyperplane η)) (alg.toCoefficients.gamma a.test) := by
  have hq : Nonempty Q := by
    by_contra hn
    have : IsEmpty Q := not_nonempty_iff.mp hn
    exact hη (by ext q; exact isEmptyElim q)
  have := hq
  refine alg.isPointWord_of_fixedColumn_support η hη h1 _ ?_ a.first ?_
  · intro he
    exact a.test_ne_zero (alg.gamma_injective (by simpa using he))
  · exact fun i hi ↦ a.U_mem hi

/-- Физический тест атома принадлежит D при любой нормировке с единицей. -/
theorem test_mem_conductor (a : PhysicalAtom alg) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η)) :
    alg.toCoefficients.gamma a.test ∈ conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) :=
  (a.isPointWord η hη h1).mem_conductor ⟨a.test, rfl⟩

end MMRank.ExactAlgorithm.PhysicalAtom
