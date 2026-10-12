import MMRank.LocalPairReplacement
import MMRank.LengthTwenty

/-! # Суммы рангов и ненулевость после точной локальной замены -/

namespace MMRank
open Matrix Module
open scoped Classical

namespace ExactAlgorithm
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- При длине20 ни один коэффициент точного333 не может исчезнуть.
В частности, это относится к новым выходам после любой точной замены. -/
theorem nonzeroTerms_of_length_twenty (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I = 20) : alg.toCoefficients.NonzeroTerms := by
  classical
  intro i
  by_contra hn
  let c : ExactAlgorithm K P Q S {j : I // j ≠ i} := {
    U := fun j ↦ alg.U j
    V := fun j ↦ alg.V j
    W := fun j ↦ alg.W j
    exact_formula := by
      intro A B
      rw [alg.exact_formula A B]
      apply Finset.sum_congr_set {j | j ≠ i} _ _ (fun _ _ ↦ rfl)
      intro j hj
      have he : j = i := by simpa using hj
      subst j
      simp only [not_and_or, ne_eq, not_not] at hn
      rcases hn with hu | hv | hw
      · simp [hu]
      · simp [hv]
      · simp [hw] }
  have hb := c.length_bound_twenty hp hq hs
  have hc := Fintype.card_subtype_lt (p := fun j : I ↦ j ≠ i) (x := i) (by simp)
  omega

end ExactAlgorithm
end MMRank
