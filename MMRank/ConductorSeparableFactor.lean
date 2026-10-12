import MMRank.ConductorJointSymmetry
import MMRank.ProportionalBlockFactor
import MMRank.JointSymmetrizerCodomain

/-! # Разделённые факторы второго физического кондуктора

Поленезависимое следствие при dim E≥5. Отсутствие делителей нуля
не предполагается для нового семейства, а выводится из координатного NZ.
-/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] [Nonempty P]

theorem hyperplaneSecondConductorFamily_injective_input [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ b ∈ alg.toCoefficients.betaInto (coordinateHyperplane η),
      a * b = 0 → a = 0 ∨ b = 0)
    (z : conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) (hz : z ≠ 0) :
    Function.Injective (alg.hyperplaneSecondConductorFamily η z) := by
  intro u v h
  apply hyperplaneInput_injective η hη
  apply alg.secondConductorMatrix_injective_input (coordinateHyperplane η) h1 hnz z
    (fun h ↦ hz (Subtype.ext h))
  apply Subtype.ext
  apply rowLinearEquiv.injective
  exact h

theorem hyperplaneSecondConductorFamily_nz [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ b ∈ alg.toCoefficients.betaInto (coordinateHyperplane η),
      a * b = 0 → a = 0 ∨ b = 0) :
    ∀ z u, alg.hyperplaneSecondConductorFamily η z u = 0 → z = 0 ∨ u = 0 := by
  intro z u h
  by_cases hz : z = 0
  · exact Or.inl hz
  · right
    apply alg.hyperplaneSecondConductorFamily_injective_input η hη h1 hnz z hz
    simpa using h

theorem hyperplaneSecondConductorFamily_mem
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (z) (u : P → K) (s : S → K) :
    alg.hyperplaneSecondConductorFamily η z u s ∈ coordinateHyperplane η := by
  exact alg.secondConductorLinearFamily_range_le (coordinateHyperplane η) z
    (hyperplaneInput η u) ⟨s, rfl⟩

variable [Nonempty Q]

end MMRank.ExactAlgorithm
