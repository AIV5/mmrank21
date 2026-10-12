import MMRank.ConductorLinearFamilies
import MMRank.HyperplaneConductorFamily
import MMRank.CoordinateJointSymmetrizers
import MMRank.JointSymmetrizerPairCapacity

/-! # Физическая оболочка в пространстве совместных симметризаторов

Взаимность первого кондуктора и закон двух кондукторов используются
одновременно. Ни размер 3, ни NZ, ни замкнутость поля для включения не нужны.
-/

namespace MMRank.ExactAlgorithm
open Module Matrix
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] [Nonempty P] [Nonempty Q]

/-- Второй кондуктор с физическим параметром u вместо входа u⊗η. -/
noncomputable def hyperplaneSecondConductorFamily (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) :
    conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) →ₗ[K]
      (P → K) →ₗ[K] (S → K) →ₗ[K] (Q → K) where
  toFun z := (alg.secondConductorLinearFamily (coordinateHyperplane η) z).comp (hyperplaneInput η)
  map_add' z w := by ext u s q; simp
  map_smul' a z := by ext u s q; simp

/-- Каждый порождающий физический тест симметризует второе семейство. -/
theorem conductor_value_mem_jointSymmetrizer (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (hη : η ≠ 0)
    (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) (u : P → K) :
    alg.hyperplaneConductorFamily η d u ∈
      jointSymmetrizer (alg.hyperplaneSecondConductorFamily η) := by
  apply reciprocal_family_mem_jointSymmetrizer _ _
    (alg.hyperplaneConductorFamily_symmetric η hη d) _ u
  intro z x y
  exact alg.conductorLinearFamilies_compatible (coordinateHyperplane η) d z
    (hyperplaneInput η x) (hyperplaneInput η y)

/-- Вся физическая оболочка, а не только одно Cδ, лежит в Σ. -/
theorem conductorPhysicalSpace_le_jointSymmetrizer (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (hη : η ≠ 0) :
    (conductorPhysicalSpace alg.toCoefficients.gamma
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))).map rowLinearEquiv.toLinearMap ≤
      jointSymmetrizer (alg.hyperplaneSecondConductorFamily η) := by
  rw [Submodule.map_le_iff_le_comap, alg.conductorPhysicalSpace_eq_span_hyperplane η hη]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨d, u⟩, rfl⟩
  exact alg.conductor_value_mem_jointSymmetrizer η hη d u

/-- Размерность Σ не меньше размерности насыщенной оболочки A_F D. -/
theorem saturated_finrank_le_jointSymmetrizer (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (hη : η ≠ 0) :
    finrank K (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range
        (alg.toCoefficients.alphaOn (coordinateHyperplane η))) ≤
      finrank K (jointSymmetrizer (alg.hyperplaneSecondConductorFamily η)) := by
  have hh := Submodule.finrank_mono (alg.conductorPhysicalSpace_le_jointSymmetrizer η hη)
  rw [LinearEquiv.finrank_map_eq, finrank_conductorPhysicalSpace _ alg.gamma_injective] at hh
  exact hh

end MMRank.ExactAlgorithm
