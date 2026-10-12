import MMRank.CommonLineRigidity
import MMRank.SecondConductor
import MMRank.RankFactorization

set_option backward.isDefEq.respectTransparency false

/-! # Симметричное семейство кондуктора на физических параметрах -/

namespace MMRank.ExactAlgorithm

open Module Matrix

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] [Nonempty Q]

/-- C(u) как линейное отображение на строках, для входа u⊗η. -/
noncomputable def hyperplaneConductorFamily (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) :
    (P → K) →ₗ[K] ((P → K) →ₗ[K] (S → K)) :=
  rowLinearEquiv.toLinearMap.comp
    ((alg.conductorMatrix (coordinateHyperplane η) d).comp (hyperplaneInput η))

@[simp] theorem hyperplaneConductorFamily_apply (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) (x : P → K) :
    alg.hyperplaneConductorFamily η d x =
      (alg.conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η x)).vecMulLinear := by
  simp [hyperplaneConductorFamily]

theorem hyperplaneConductorFamily_symmetric (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (hη : η ≠ 0) (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) (x y : P → K) :
    alg.hyperplaneConductorFamily η d x y = alg.hyperplaneConductorFamily η d y x := by
  simpa only [hyperplaneConductorFamily_apply, Matrix.vecMulLinear_apply] using
    alg.conductorMatrix_hyperplane_reciprocity η hη d x y

variable [Nonempty P]

end MMRank.ExactAlgorithm
