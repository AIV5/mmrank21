module

public import MMRank.CoefficientMaps
public import MMRank.LengthReduction

@[expose] public section

/-! # Транспонирующая симметрия точного алгоритма -/

namespace MMRank
open Matrix
variable {K P Q S I : Type*}

/-- Отражение цикла: (U,V,W) ↦ (Uᵀ,Wᵀ,Vᵀ), формат (P,Q,S) ↦ (Q,P,S). -/
def Coefficients.reflect (d : Coefficients K P Q S I) : Coefficients K Q P S I where
  U i := (d.U i).transpose
  V i := (d.W i).transpose
  W i := (d.V i).transpose

@[simp] theorem Coefficients.reflect_reflect (d : Coefficients K P Q S I) :
    d.reflect.reflect = d := by cases d; rfl

variable [CommSemiring K] [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Точность отражения следует из циклической точности и транспонирования. -/
def ExactAlgorithm.reflect (d : ExactAlgorithm K P Q S I) : ExactAlgorithm K Q P S I where
  toCoefficients := d.toCoefficients.reflect
  exact_formula := by
    intro A B
    have hU (i) : trace ((d.U i).transpose * A) = trace (d.U i * A.transpose) :=
      trace_transpose_mul (d.U i) A.transpose
    have hW (i) : trace ((d.W i).transpose * B) = trace (d.W i * B.transpose) :=
      trace_transpose_mul (d.W i) B.transpose
    have hh := congrArg Matrix.transpose (d.rotate.rotate.exact_formula B.transpose A.transpose)
    simpa [Coefficients.evaluate, Coefficients.reflect, ExactAlgorithm.rotate,
      transpose_sum, transpose_smul, transpose_mul, hU, hW, mul_comm] using hh

@[simp] theorem ExactAlgorithm.reflect_reflect (d : ExactAlgorithm K P Q S I) :
    d.reflect.reflect = d := by cases d; rfl

omit [Fintype Q] [Fintype I] in
theorem Coefficients.beta_reflect (d : Coefficients K P Q S I) (B : Matrix S P K) :
    d.reflect.beta B = d.gamma B.transpose := by
  ext i
  exact trace_transpose_mul (d.W i) B.transpose

end MMRank
