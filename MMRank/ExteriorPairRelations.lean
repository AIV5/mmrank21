module

public import MMRank.InputRadical
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-! # Внешние отношения подстановки и размерностный бюджет -/

namespace MMRank
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Простая пара αᵢ|_{A:F A=0} и Wᵢ как линейное отображение.
Это модель простого тензора, без выбора координат ограниченного входа. -/
noncomputable def Coefficients.restrictedPair (d : Coefficients K P Q S I)
    (F : Submodule K (Q → K)) (i : I) : matricesKilling (P := P) F →ₗ[K] Matrix S P K :=
  ((LinearMap.proj i).comp (d.alpha.domRestrict (matricesKilling F))).smulRight (d.W i)

/-- Сумма внешних простых пар с переменными коэффициентами. -/
noncomputable def Coefficients.externalPairSum (d : Coefficients K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I) :
    (↥(Gᶜ) → K) →ₗ[K] (matricesKilling (P := P) F →ₗ[K] Matrix S P K) := by
  classical
  exact Fintype.linearCombination K (fun i : ↥(Gᶜ) ↦ d.restrictedPair F i.val)

namespace ExactAlgorithm

/-- На входах, зануляющих F, остаются только внешние слагаемые,
для произвольного второго входа B. -/
theorem restricted_exact_formula (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I)
    (hG : ∀ i ∈ G, alg.U i ∈ matricesInto (S := P) F)
    (A : matricesKilling (P := P) F) (B : Matrix S Q K) :
    B * A.val = ∑ i : ↥(Gᶜ),
      (alg.toCoefficients.alpha A.val i * alg.toCoefficients.beta B i) • alg.W i := by
  classical
  rw [alg.exact_formula]
  apply Finset.sum_congr_set Gᶜ _ _ (fun _ _ ↦ rfl)
  intro i hi
  simp only [Set.mem_compl_iff, not_not] at hi
  have hz : alg.toCoefficients.alpha A.val i = 0 := by
    change trace (alg.U i * A.val) = 0
    rw [mul_eq_zero_of_restricted F A.val (alg.U i) A.property (hG i hi), trace_zero]
  change trace (alg.U i * A.val) = 0 at hz
  simp [hz]

/-- Внешние значения β на E_F дают настоящие линейные отношения
между внешними парами. Достаточно, что каждый внутренний Uᵢ имеет образ в F. -/
theorem externalBeta_range_le_pairSum_ker (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I)
    (hG : ∀ i ∈ G, alg.U i ∈ matricesInto (S := P) F) :
    (alg.toCoefficients.externalBeta F G).range ≤ (alg.toCoefficients.externalPairSum F G).ker := by
  classical
  rintro _ ⟨B, rfl⟩
  apply LinearMap.ext
  intro A
  have he := alg.restricted_exact_formula F G hG A B.val
  rw [mul_eq_zero_of_restricted F A.val B.val A.property B.property] at he
  change (∑ i : ↥(Gᶜ), alg.toCoefficients.beta B.val i.val • alg.toCoefficients.restrictedPair F i.val) A = 0
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Coefficients.restrictedPair,
    LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.domRestrict_apply, smul_smul, mul_comm] using he.symm

/-- Пространство внешних отношений имеет размерность dim E_F−dim Z_F;
его вложение в ядро суммы пар даёт ранговый бюджет без аддитивности ранга. -/
theorem exterior_pair_budget (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I)
    (hG : ∀ i ∈ G, alg.U i ∈ matricesInto (S := P) F) :
    finrank K (alg.toCoefficients.externalPairSum F G).range +
        Fintype.card S * finrank K F ≤
      Gᶜ.ncard + finrank K (alg.toCoefficients.inputRadical F G) := by
  classical
  have hi := Submodule.finrank_mono (alg.externalBeta_range_le_pairSum_ker F G hG)
  have hp := (alg.toCoefficients.externalPairSum F G).finrank_range_add_finrank_ker
  have hb := alg.toCoefficients.finrank_externalBeta_add_radical F G
  rw [Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard] at hp
  omega

theorem slice_mem_externalPairSum_range (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I)
    (hG : ∀ i ∈ G, alg.U i ∈ matricesInto (S := P) F) (B : Matrix S Q K) :
    (mulLeftLinearMap P K B).domRestrict (matricesKilling F) ∈
      (alg.toCoefficients.externalPairSum F G).range := by
  classical
  refine ⟨fun i ↦ alg.toCoefficients.beta B i, ?_⟩
  ext A s p
  have hh := congrFun (congrFun (alg.restricted_exact_formula F G hG A B) s) p
  simpa [Coefficients.externalPairSum, Fintype.linearCombination_apply,
    Coefficients.restrictedPair, Matrix.sum_apply, smul_smul, mul_comm] using hh.symm

end ExactAlgorithm
end MMRank
