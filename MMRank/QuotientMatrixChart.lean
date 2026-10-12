import MMRank.RestrictedInputs

/-! # Матричные координаты фактора по подпространству -/

namespace MMRank
open Matrix Module
variable {K Q : Type*} [Field K] [Fintype Q]

/-- Координаты фактора и линейное сечение, в порядке правого действия.
Не выбирается дополнение в качестве новой математической предпосылки. -/
theorem exists_quotient_matrix_chart (F : Submodule K (Q → K)) :
    ∃ D : Matrix Q (Fin (finrank K ((Q → K) ⧸ F))) K,
    ∃ C : Matrix (Fin (finrank K ((Q → K) ⧸ F))) Q K,
      C * D = 1 ∧ F ≤ D.vecMulLinear.ker := by
  classical
  let e := (Module.finBasis K ((Q → K) ⧸ F)).equivFun
  let f := e.toLinearMap.comp F.mkQ
  have hf : Function.Surjective f := e.surjective.comp F.mkQ_surjective
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let D : Matrix Q (Fin (finrank K ((Q → K) ⧸ F))) K := rowLinearEquiv.symm f
  let C : Matrix (Fin (finrank K ((Q → K) ⧸ F))) Q K := rowLinearEquiv.symm g
  have hD : D.vecMulLinear = f := by rw [← rowLinearEquiv_apply]; exact rowLinearEquiv.apply_symm_apply f
  have hC : C.vecMulLinear = g := by rw [← rowLinearEquiv_apply]; exact rowLinearEquiv.apply_symm_apply g
  refine ⟨D, C, ?_, ?_⟩
  · apply rowLinearEquiv.injective
    rw [rowLinearEquiv_apply, rowLinear_mul, hD, hC, hg]
    ext x j
    simp
  · intro x hx
    change D.vecMulLinear x = 0
    rw [hD]
    have hz : F.mkQ x = 0 := by simpa using hx
    change e (F.mkQ x) = 0
    rw [hz, map_zero]

end MMRank
