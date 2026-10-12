module

public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

/-!
# At least 21 products for exact 3 × 3 matrix multiplication

For every field K, every finite exact bilinear algorithm for ordinary 3 × 3
matrix multiplication uses at least 21 products of input linear forms.
The two families of linear forms and the output matrices are arbitrary;
there are no nonzero-term, minimality, or coefficient-rank hypotheses.
The statement includes every characteristic and finite fields. It concerns
exact bilinear complexity, not border rank or general arithmetic circuits.

This statement imports only Mathlib. Its deliberate proof hole is confined
to this Challenge; Comparator checks the proved version in Solution separately.
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
  sorry
