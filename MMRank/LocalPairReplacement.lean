module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Module.BigOperators
public import MMRank.CoefficientMaps
public import MMRank.TraceDuality

@[expose] public section

namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [CommSemiring K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Простая пара первых двух следовых форм; оба входа остаются независимыми. -/
def matrixCoefficientPair (U : Matrix P Q K) (V : Matrix Q S K) :
    Matrix Q P K →ₗ[K] Matrix S Q K →ₗ[K] K :=
  ((traceLinearMap P K K).comp (mulLeftLinearMap P K U)).smulRight
    ((traceLinearMap Q K K).comp (mulLeftLinearMap Q K V))

@[simp] theorem matrixCoefficientPair_apply (U : Matrix P Q K) (V : Matrix Q S K)
    (A : Matrix Q P K) (B : Matrix S Q K) :
    matrixCoefficientPair U V A B = trace (U * A) * trace (V * B) := rfl

end MMRank
