import MMRank.ProjectedTestPairs
import MMRank.CollinearSimplePairs
import MMRank.StationaryConductorPlane

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Nonempty Q]

/-- Взаимное семейство кондукторного слова задаёт нижнюю оценку
совместной колонковой оболочки всех поддержанных тестов. -/
theorem conductor_rank_le_supportedTests_columnSpan
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) :
    finrank K ((alg.toCoefficients.alphaOn (coordinateHyperplane η)).map (LinearMap.mulRight K d.val)) ≤
      finrank K (matrixColumnSpan (alg.toCoefficients.supportedTests {i | d.val i ≠ 0})) := by
  let C := (alg.conductorMatrix (coordinateHyperplane η) d).comp (hyperplaneInput η)
  have hr : C.range = (alg.conductorMatrix (coordinateHyperplane η) d).range := by
    ext D
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨hyperplaneInput η x, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨x, rfl⟩ := hyperplaneInput_surjective η hη A
      exact ⟨x, rfl⟩
  have hle : C.range ≤ alg.toCoefficients.supportedTests {i | d.val i ≠ 0} := by
    rintro _ ⟨x, rfl⟩
    rw [Coefficients.mem_supportedTests]
    intro i hi
    change alg.toCoefficients.gamma (alg.conductorMatrix _ d (hyperplaneInput η x)) i = 0
    rw [alg.gamma_conductorMatrix]
    simp only [Set.mem_ofPred_eq, not_not] at hi
    simp [hi]
  have hcols : matrixColumnSpan C.range ≤
      matrixColumnSpan (alg.toCoefficients.supportedTests {i | d.val i ≠ 0}) := by
    apply iSup_le
    intro D
    exact le_iSup (fun D : alg.toCoefficients.supportedTests {i | d.val i ≠ 0} ↦
      D.val.transpose.vecMulLinear.range) ⟨D.val, hle D.property⟩
  have hd := Submodule.finrank_mono hcols
  rw [finrank_reciprocal_columnSpan C (fun x y ↦
    (alg.conductorMatrix_hyperplane_reciprocity η hη d x y).symm),
    hr, alg.finrank_conductorMatrix_range] at hd
  exact hd

end MMRank.ExactAlgorithm
