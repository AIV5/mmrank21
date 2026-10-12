module

public import MMRank.LengthTwentyOne

@[expose] public section

/-!
# A lower bound of 21 for 3 × 3 matrix multiplication over every field

The statement below uses arbitrary
linear input forms and ordinary matrix multiplication, so readers need not
unfold the internal `ExactAlgorithm` structure to inspect its hypotheses.
The proof only translates conventions and applies the exact-algorithm theorem.
-/

namespace MMRank
open scoped BigOperators

/-- Over any field, an exact bilinear algorithm for 3 × 3 matrix multiplication
has at least 21 scalar products. The input linear forms and output matrices
are unrestricted; zero terms are allowed. -/
theorem matrix_multiplication_length_ge_twenty_one
    {K I : Type*} [Field K] [Fintype I]
    (a b : I → (Matrix (Fin 3) (Fin 3) K →ₗ[K] K))
    (W : I → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      A * B = ∑ i, (a i A * b i B) • W i) :
    21 ≤ Fintype.card I := by
  classical
  have hb := fun i ↦ (exists_unique_trace_representation (b i)).exists
  have ha := fun i ↦ (exists_unique_trace_representation (a i)).exists
  choose U hU using hb
  choose V hV using ha
  let alg : ExactAlgorithm K (Fin 3) (Fin 3) (Fin 3) I := {
    U := U
    V := V
    W := W
    exact_formula := by
      intro A B
      change B * A = ∑ i, (Matrix.trace (U i * A) * Matrix.trace (V i * B)) • W i
      rw [h B A]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.trace_mul_comm (U i) A, Matrix.trace_mul_comm (V i) B,
        ← hU i A, ← hV i B, mul_comm (a i B) (b i A)] }
  exact alg.length_bound_twenty_one rfl rfl rfl

end MMRank
