import MMRank.GenericMatrixDirections
import MMRank.PointWordPhysical
import MMRank.SupportedTestSpan

/-! # Полная коэффициентная оболочка точечного направления -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Нормировка задаёт один функционал, принимающий значение один
на всех оценённых первых направлениях. -/
theorem exists_normalizing_row (alg : ExactAlgorithm K P Q S I)
    (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η)) :
    ∃ u : P → K, ∀ i, u ⬝ᵥ (alg.U i *ᵥ η) = 1 := by
  obtain ⟨A, hA, he⟩ := h1
  obtain ⟨u, hu⟩ := hyperplaneInput_surjective η hη ⟨A, hA⟩
  refine ⟨u, fun i ↦ ?_⟩
  rw [← Coefficients.alpha_hyperplaneInput_apply]
  rw [hu]
  exact congrFun he i

end MMRank.ExactAlgorithm
