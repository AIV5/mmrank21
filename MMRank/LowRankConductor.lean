module

public import MMRank.SecondConductor
public import MMRank.RankFactorization
public import MMRank.CommonLineRigidity

@[expose] public section

/-! # Исключение промежуточного ранга первого кондуктора

Общий одномерный образ и закон двух кондукторов ограничивают весь A_F Z,
а насыщенный рост противоречит этой верхней оценке.
-/

namespace MMRank

open Module Matrix

set_option backward.isDefEq.respectTransparency false

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Размерность матриц S→Q, зануляющих L и имеющих образ в F. -/
theorem finrank_matricesKilling_inf_matricesInto_le
    (L : Submodule K (S → K)) (F : Submodule K (Q → K)) :
    finrank K ↥(matricesKilling (P := Q) L ⊓ matricesInto (S := S) F) ≤
      (Fintype.card S - finrank K L) * finrank K F := by
  let T := matricesKilling (P := Q) L ⊓ matricesInto (S := S) F
  let f : T →ₗ[K] ((S → K) →ₗ[K] (Q → K)) := rowLinearEquiv.toLinearMap.comp T.subtype
  have h := finrank_le_annihilator_capacity L F f
    (rowLinearEquiv.injective.comp Subtype.val_injective)
    (fun t ↦ by simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      rowLinearEquiv_apply, Submodule.subtype_apply] using (mem_matricesInto F t.val).mp t.property.2)
    (fun t ↦ by simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      rowLinearEquiv_apply, Submodule.subtype_apply] using (mem_matricesKilling L t.val).mp t.property.1)
  simpa only [Module.finrank_pi, finrank_self, Nat.mul_one] using h

namespace ExactAlgorithm

variable [Nonempty P] [Nonempty Q] [Nonempty S]

omit [Nonempty Q] [Nonempty S] in
/-- Вместимость произведений M'Z для любого подпространства M'⊆A_F,
если соответствующие вторые подъёмы зануляют L. -/
theorem second_product_capacity_of_subspace (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K)) (M' : Submodule K (ι → K))
    (hM' : M' ≤ alg.toCoefficients.alphaOn F) (L : Submodule K (S → K))
    (hk : ∀ A : matricesKilling (P := P) F, alg.toCoefficients.alpha A.val ∈ M' →
      ∀ z, L ≤ (alg.secondConductorMatrix F z A).val.vecMulLinear.ker) :
    finrank K (M' * conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F)) ≤
      (Fintype.card S - finrank K L) * finrank K F := by
  let T := matricesKilling (P := Q) L ⊓ matricesInto (S := S) F
  have hm : M' * conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F) ≤
      T.map alg.toCoefficients.beta := by
    apply Submodule.mul_le.mpr
    intro a ha z hz
    obtain ⟨A, hA, rfl⟩ := Submodule.mem_map.mp (hM' ha)
    refine ⟨(alg.secondConductorMatrix F ⟨z, hz⟩ ⟨A, hA⟩).val, ?_, ?_⟩
    · exact ⟨(mem_matricesKilling L _).mpr (hk ⟨A, hA⟩ ha ⟨z, hz⟩),
        (alg.secondConductorMatrix F ⟨z, hz⟩ ⟨A, hA⟩).property⟩
    · exact alg.beta_secondConductorMatrix F ⟨z, hz⟩ ⟨A, hA⟩
  exact (Submodule.finrank_mono hm).trans
    ((Submodule.finrank_map_le _ _).trans (finrank_matricesKilling_inf_matricesInto_le L F))

end ExactAlgorithm
end MMRank
