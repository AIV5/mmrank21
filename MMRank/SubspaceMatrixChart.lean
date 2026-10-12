module

public import MMRank.RestrictedInputs

@[expose] public section

namespace MMRank
open Matrix Module
variable {K P : Type*} [Field K] [Fintype P]

/-- Координаты подпространства, линейная ретракция и тождество на его строках.
Размер координат задаётся равенством размерностей, а не выбором дополнения. -/
theorem exists_subspace_matrix_chart (F : Submodule K (P → K)) (n : ℕ)
    (hn : finrank K F = n) :
    ∃ B : Matrix (Fin n) P K, ∃ D : Matrix P (Fin n) K,
      B * D = 1 ∧ B ∈ matricesInto F ∧ ∀ x ∈ F, (x ᵥ* D) ᵥ* B = x := by
  classical
  let e : F ≃ₗ[K] (Fin n → K) :=
    (Module.finBasisOfFinrankEq K F hn).equivFun
  let f : (Fin n → K) →ₗ[K] (P → K) := F.subtype.comp e.symm.toLinearMap
  have hf : Function.Injective f := F.injective_subtype.comp e.symm.injective
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let B : Matrix (Fin n) P K := rowLinearEquiv.symm f
  let D : Matrix P (Fin n) K := rowLinearEquiv.symm g
  have hB : B.vecMulLinear = f := by rw [← rowLinearEquiv_apply]; exact rowLinearEquiv.apply_symm_apply f
  have hD : D.vecMulLinear = g := by rw [← rowLinearEquiv_apply]; exact rowLinearEquiv.apply_symm_apply g
  refine ⟨B, D, ?_, ?_, ?_⟩
  · apply rowLinearEquiv.injective
    rw [rowLinearEquiv_apply, rowLinear_mul, hB, hD, hg]
    ext x i
    simp
  · apply (mem_matricesInto F B).mpr
    rw [hB]
    rintro _ ⟨x, rfl⟩
    exact (e.symm x).property
  · intro x hx
    change B.vecMulLinear (D.vecMulLinear x) = x
    rw [hB, hD]
    have he : f (e ⟨x, hx⟩) = x := by simp [f]
    rw [← he, ← LinearMap.comp_apply g f, hg, LinearMap.id_apply]

/-- Если ретракция тождественна на F, она тождественна на всех строках C. -/
theorem mul_retraction_of_rows {S N : Type*} [Fintype S] [Fintype N]
    (F : Submodule K (P → K)) (B : Matrix N P K) (D : Matrix P N K)
    (h : ∀ x ∈ F, (x ᵥ* D) ᵥ* B = x) (C : Matrix S P K)
    (hC : C ∈ matricesInto F) : (C * D) * B = C := by
  have hr := (mem_matricesInto F C).mp hC
  ext s p
  have hh := h (C s) (hr (by rw [range_vecMulLinear]; exact Submodule.subset_span (Set.mem_range_self s)))
  exact congrFun hh p

end MMRank
