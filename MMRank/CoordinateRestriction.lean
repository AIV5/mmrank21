module

public import MMRank.LinearSubstitution
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

namespace MMRank
open Module
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype I]

/-- k-мерное сечение, гасящее dim V-k независимых координат. -/
theorem exists_subspace_annihilating_coordinates
    (c : V →ₗ[K] (I → K)) (hc : Function.Injective c)
    (k : ℕ) (hk : k ≤ finrank K V) :
    ∃ (T : Submodule K V) (G : Set I), finrank K T = k ∧
      G.ncard + k = finrank K V ∧ ∀ x ∈ T, ∀ i ∈ G, c x i = 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hk
  let X := Submodule.span K (Set.range v)
  have hX : finrank K X = k := by simpa [X] using finrank_span_eq_card hv
  obtain ⟨Y, hY⟩ := X.exists_isCompl
  let e := X.prodEquivOfIsCompl Y hY
  obtain ⟨G, L, hG, hL⟩ := exists_linear_substitution
    (fun i ↦ (LinearMap.proj i).comp (c.comp e.toLinearMap)) (by
      intro y hy
      have hz : e (0, y) = 0 := hc (by ext i; simpa using hy i)
      have he : ((0 : X), y) = (0 : X × Y) := e.injective (hz.trans e.map_zero.symm)
      exact congrArg Prod.snd he)
  let f : X →ₗ[K] V := e.toLinearMap.comp ((LinearMap.id : X →ₗ[K] X).prod L)
  have hf : Function.Injective f := by
    intro x y h
    exact congrArg Prod.fst (e.injective h)
  refine ⟨f.range, G, ?_, ?_, ?_⟩
  · exact (LinearEquiv.ofInjective f hf).finrank_eq.symm.trans hX
  · have hd := Submodule.finrank_add_eq_of_isCompl hY
    omega
  · rintro _ ⟨x, rfl⟩ i hi
    exact hL i hi x

end MMRank
