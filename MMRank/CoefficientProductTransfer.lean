import MMRank.CoefficientMaps

/-! # Перенос равенств координатных произведений в физические матрицы

Точность алгоритма отражает равенство β(B)γ(C) в равенство CB.
Два других порядка получаются циклическим сдвигом того же доказательства.
-/

namespace MMRank.ExactAlgorithm

open Matrix
open scoped BigOperators

variable {K P Q S ι : Type*} [CommSemiring K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Точность переносит также линейное соотношение между произведениями. -/
theorem sum_mul_eq_zero_of_sum_beta_mul_gamma_eq_zero {T : Type*} [Fintype T]
    (alg : ExactAlgorithm K P Q S ι) (B : T → Matrix S Q K) (C : T → Matrix P S K)
    (h : ∑ t, alg.toCoefficients.beta (B t) * alg.toCoefficients.gamma (C t) = 0) :
    ∑ t, C t * B t = 0 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  have ht (t : T) := alg.trace_identity A (B t) (C t)
  simp only [Matrix.sum_mul, Matrix.trace_sum, ht,
    Matrix.zero_mul, Matrix.trace_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have hi := congrFun h i
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.zero_apply] at hi
  change ∑ t, trace (alg.U i * A) * trace (alg.V i * B t) * trace (alg.W i * C t) = 0
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change trace (alg.U i * A) * (∑ t, alg.toCoefficients.beta (B t) i *
    alg.toCoefficients.gamma (C t) i) = 0
  rw [hi, mul_zero]

/-- Координатное произведение вторых и третьих слов определяет физическое CB. -/
theorem mul_eq_of_beta_mul_gamma_eq (alg : ExactAlgorithm K P Q S ι)
    (B B' : Matrix S Q K) (C C' : Matrix P S K)
    (h : alg.toCoefficients.beta B * alg.toCoefficients.gamma C =
      alg.toCoefficients.beta B' * alg.toCoefficients.gamma C') : C * B = C' * B' := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [alg.trace_identity, alg.trace_identity]
  apply Finset.sum_congr rfl
  intro i _
  have hi := congrFun h i
  change trace (alg.V i * B) * trace (alg.W i * C) =
    trace (alg.V i * B') * trace (alg.W i * C') at hi
  rw [mul_assoc, hi, ← mul_assoc]

end MMRank.ExactAlgorithm
