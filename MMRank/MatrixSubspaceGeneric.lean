import MMRank.GenericMatrixDirections
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace MMRank
open Matrix MvPolynomial
variable {K P Q I J : Type*} [Field K] [Fintype Q]

/-- Значение U_iη отражает принадлежность любому из заданного семейства
постоянных подпространств. -/
def MatrixSubspaceGeneric (U : I → Matrix P Q K) (F : J → Submodule K (P → K))
    (η : Q → K) : Prop :=
  ∀ j i, U i *ᵥ η ∈ F j → ∀ x, U i *ᵥ x ∈ F j

/-- Свидетель общности относительно всех заданных подпространств. -/
theorem polynomial_open_matrixSubspaceGeneric [Fintype I]
    {J : Type*} [Fintype J] (U : I → Matrix P Q K) (F : J → Submodule K (P → K)) :
    ∃ g : MvPolynomial Q K, g ≠ 0 ∧ ∀ η, eval η g ≠ 0 → MatrixSubspaceGeneric U F η := by
  classical
  let Bad := {t : J × I // ∃ x, U t.2 *ᵥ x ∉ F t.1}
  have hw (t : Bad) : ∃ x, ∃ φ : (P → K) →ₗ[K] K,
      φ (U t.val.2 *ᵥ x) ≠ 0 ∧ F t.val.1 ≤ φ.ker := by
    obtain ⟨x, hx⟩ := t.property
    obtain ⟨φ, hφ, hk⟩ := Submodule.exists_le_ker_of_notMem hx
    exact ⟨x, φ, hφ, hk⟩
  choose x φ hφ hk using hw
  let f (t : Bad) : MvPolynomial Q K :=
    ∑ q, C (φ t (fun p ↦ U t.val.2 p q)) * X q
  have he (t : Bad) (y : Q → K) : eval y (f t) = φ t (U t.val.2 *ᵥ y) := by
    have hh : U t.val.2 *ᵥ y = ∑ q, y q • (fun p ↦ U t.val.2 p q) := by
      ext p
      simp [mulVec, dotProduct, mul_comm]
    simp [f, hh, map_sum, mul_comm]
  have hf (t : Bad) : f t ≠ 0 := by
    intro hz
    exact hφ t (by rw [← he, hz, map_zero])
  obtain ⟨g, hg, hgood⟩ := polynomial_open_finset f hf
  refine ⟨g, hg, ?_⟩
  intro η hη j i hm y
  by_contra hn
  let t : Bad := ⟨(j, i), y, hn⟩
  have hh := hgood η hη t
  rw [he] at hh
  exact hh (hk t hm)

end MMRank
