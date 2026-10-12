import MMRank.SecondConductorProductRank

/-! # Бюджет длины из разделённого второго кондуктора

Независимость физических вторых факторов отражает любое соотношение γ·Z
в нулевые матричные коэффициенты. Ранги отдельных Vᵢ, общий выбор η,
простые диагональные тесты и замкнутость поля не нужны.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped BigOperators
variable {K P Q S I T : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Fintype T] [Nonempty P]

/-- Сюръективный первый фактор и инъективный второй обеспечивают полную
независимость γ·Z с произвольными матричными коэффициентами. -/
theorem gammaWordSum_injective_of_separable_secondConductor
    (alg : ExactAlgorithm K P Q S I) (η : Q → K)
    (L : (P → K) →ₗ[K] (S → K)) (hL : Function.Surjective L)
    (f : conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) →ₗ[K] coordinateHyperplane η)
    (hf : Function.Injective f)
    (hfactor : ∀ z u,
      (alg.secondConductorMatrix (coordinateHyperplane η) z (hyperplaneInput η u)).val =
        vecMulVec (L u) (f z).val)
    (z : T → conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (hz : LinearIndependent K z) :
    Function.Injective (alg.gammaWordSum (fun a ↦ (z a).val)) := by
  classical
  have hzf := (hz.map' f (LinearMap.ker_eq_bot.mpr hf)).map'
    (coordinateHyperplane η).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  apply (injective_iff_map_eq_zero _).mpr
  intro C hC
  change ∑ a, alg.toCoefficients.gamma (C a) * (z a).val = 0 at hC
  have hcoord (p : P) (u : P → K) (a : T) : (C a *ᵥ L u) p = 0 := by
    let B a := (alg.secondConductorMatrix (coordinateHyperplane η) (z a)
      (hyperplaneInput η u)).val
    have hprod : ∑ a, C a * B a = 0 := by
      apply alg.sum_mul_eq_zero_of_sum_beta_mul_gamma_eq_zero
      simp_rw [show ∀ a, alg.toCoefficients.beta (B a) =
        alg.toCoefficients.alpha (hyperplaneInput η u).val * (z a).val
        from fun _ ↦ alg.beta_secondConductorMatrix _ _ _,
        mul_assoc, mul_comm ((z _).val)]
      rw [← Finset.mul_sum, hC, mul_zero]
    have hsum : ∑ a, (C a *ᵥ L u) p • (f (z a)).val = 0 := by
      ext q
      have hh := congrArg (fun A : Matrix P Q K ↦ A p q) hprod
      simpa only [B, hfactor, mul_vecMulVec, Matrix.sum_apply, vecMulVec_apply,
        Matrix.zero_apply, Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh
    exact Fintype.linearIndependent_iff.mp hzf (fun a ↦ (C a *ᵥ L u) p) hsum a
  funext a
  ext p s
  obtain ⟨u, hu⟩ := hL (Pi.single s 1)
  simpa only [hu, mulVec_single_one, col_apply, Pi.zero_apply, Matrix.zero_apply] using hcoord p u a

omit [Fintype T] in
/-- Разделённый второй кондуктор даёт длину≥p s dim Z+dim M.
Предполагаются только нормировка, сюръективность L и инъективность f. -/
theorem length_bound_of_separable_secondConductor
    (alg : ExactAlgorithm K P Q S I) (η : Q → K)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (L : (P → K) →ₗ[K] (S → K)) (hL : Function.Surjective L)
    (f : conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) →ₗ[K] coordinateHyperplane η)
    (hf : Function.Injective f)
    (hfactor : ∀ z u,
      (alg.secondConductorMatrix (coordinateHyperplane η) z (hyperplaneInput η u)).val =
        vecMulVec (L u) (f z).val) :
    Fintype.card P * Fintype.card S *
      finrank K (conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
        (alg.toCoefficients.alphaOn (coordinateHyperplane η))) +
      finrank K (alg.toCoefficients.alphaOn (coordinateHyperplane η)) ≤ Fintype.card I := by
  classical
  let F := coordinateHyperplane η
  let M := alg.toCoefficients.alphaOn F
  let Z := conductor (alg.toCoefficients.betaInto F) M
  let z := Module.finBasis K Z
  let W := alg.gammaWordSum (fun a ↦ (z a).val)
  have hi : Function.Injective W := alg.gammaWordSum_injective_of_separable_secondConductor
    η L hL f hf hfactor z z.linearIndependent
  have hr : W.range ≤ coordinateOrthogonal M := by
    rintro _ ⟨C, rfl⟩
    change ∑ a, alg.toCoefficients.gamma (C a) * (z a).val ∈ coordinateOrthogonal M
    apply Submodule.sum_mem
    intro a _
    apply Submodule.mem_orthogonalBilin.mpr
    intro m hm
    have hzB := conductor_le_of_one_mem (alg.toCoefficients.betaInto F) M h1 (z a).property
    have hh := alg.restricted_triple_sum_eq_zero F hm hzB ⟨C a, rfl⟩
    simpa [dotProductBilin, dotProduct, mul_assoc, mul_comm, mul_left_comm] using hh
  have hd := Submodule.finrank_mono hr
  rw [LinearMap.finrank_range_of_inj hi, finrank_coordinateOrthogonal] at hd
  have hdom : finrank K (Fin (finrank K Z) → Matrix P S K) =
      Fintype.card P * Fintype.card S * finrank K Z := by
    simp [Module.finrank_pi_fintype, Module.finrank_matrix, mul_comm]
  rw [hdom] at hd
  have hm := M.finrank_le
  rw [Module.finrank_pi] at hm
  change Fintype.card P * Fintype.card S * finrank K Z + finrank K M ≤ Fintype.card I
  omega

end MMRank.ExactAlgorithm
