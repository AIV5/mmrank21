import MMRank.RestrictedSupport
import MMRank.ConductorSeparableFactor
import Mathlib.LinearAlgebra.Projection

/-! # Следовые координаты разделённого второго кондуктора -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]
  [Nonempty P]

/-- Физическая формула на строках определяет саму матрицу подъёма. -/
theorem secondConductorMatrix_eq_outer_of_factor
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K)
    (L : (P → K) →ₗ[K] (S → K))
    (f : conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) →ₗ[K] coordinateHyperplane η)
    (hf : ∀ z u s, alg.hyperplaneSecondConductorFamily η z u s =
      (s ⬝ᵥ L u) • (f z).val) (z) (u : P → K) :
    (alg.secondConductorMatrix (coordinateHyperplane η) z (hyperplaneInput η u)).val =
      vecMulVec (L u) (f z).val := by
  apply rowLinearEquiv.injective
  apply LinearMap.ext
  intro s
  simpa only [rowLinearEquiv_apply, Matrix.vecMulLinear_apply, vecMul_vecMulVec,
    hyperplaneSecondConductorFamily, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, secondConductorLinearFamily_apply] using hf z u s

end MMRank.ExactAlgorithm
