module

public import MMRank.PublicTheorem

public section

/-!
# Proved version of the Palomar statement

This theorem applies the public interface of the full proof development.
It does not import Challenge and uses no assumed project axiom.
-/

open scoped BigOperators

/-- An unrestricted exact bilinear decomposition of 3 × 3 matrix
multiplication over a field has at least 21 terms. -/
theorem MMRank.Palomar.lower_bound
    {K I : Type*} [Field K] [Fintype I]
    (a b : I → (Matrix (Fin 3) (Fin 3) K →ₗ[K] K))
    (W : I → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      A * B = ∑ i, (a i A * b i B) • W i) :
    21 ≤ Fintype.card I := by
  exact MMRank.matrix_multiplication_length_ge_twenty_one a b W h
