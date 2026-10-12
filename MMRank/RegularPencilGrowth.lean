import MMRank.PlaneCoefficientChart
import MMRank.RegularSliceChoice
import MMRank.TwoDimensionalResolventGeometry
import MMRank.ResolventPairDescent
import MMRank.GrowingComponentImage

/-! # Запрет регулярной компоненты одним операторным отношением

Корранг соседей выводится
непосредственно из точности и малых классов, без расщепления пучка.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K] [IsAlgClosed K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Nonempty Q]

/-- Регулярное поддержанное двумерное пространство с малыми первыми
классами несовместимо с минимумом первой ранговой массы при333≤20. -/
theorem IsFirstRankMinimal.no_regular_plane
    {alg : ExactAlgorithm K P Q S I} (hmin : alg.IsFirstRankMinimal)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (G : Set I) (F : Submodule K (P → K))
    (hF : finrank K F = 2)
    (hcols : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F)
    (hlo : 6 ≤ G.ncard) (hhi : G.ncard ≤ 7)
    (hT : finrank K (alg.toCoefficients.supportedTests G) = 2)
    (hR : finrank K (alg.toCoefficients.supportedTestImage G) = 2)
    (hreg : ∃ C ∈ alg.toCoefficients.supportedTests G, C.rank = 2)
    (hγ : ∀ i : G, ∃ C ∈ alg.toCoefficients.supportedTests G,
      alg.toCoefficients.gamma C i ≠ 0)
    (hclass : ∀ p : P → K, p ≠ 0 →
      {i ∈ G | alg.U i ∈ fixedColumnSpace (Q := Q) p}.ncard ≤ 2) : False := by
  classical
  let T := alg.toCoefficients.supportedTests G
  let R := alg.toCoefficients.supportedTestImage G
  obtain ⟨E, L, _, j, hLE, hret, hj, hTj, hrj, _, haj⟩ := exists_two_sided_slice_chart
    (Q := Q) T F R 2 2 hF hR
    (fun C hC ↦ alg.supportedTests_columns F G hcols ⟨C, hC⟩)
    (fun C hC ↦ (mem_matricesInto R C).mpr
      (le_iSup (fun D : T ↦ D.val.vecMulLinear.range) ⟨C, hC⟩))
  let γ : Matrix P S K →ₗ[K] (G → K) :=
    (LinearMap.pi fun i : G ↦ (LinearMap.proj i.val).comp alg.toCoefficients.gamma)
  obtain ⟨C, hC, D, hD, H, _, hc, hLD, hH, hDC⟩ :=
    exists_regular_slice_pair T j L hj hTj (by change 2 ≤ finrank K (alg.toCoefficients.supportedTests G); omega) hrj haj γ hγ hreg
  let X (i : I) := L * alg.U i
  let c (i : I) := alg.toCoefficients.gamma C i
  let t (i : I) := alg.toCoefficients.gamma D i / c i
  have hU (i : G) : E * X i = alg.U i := hret _ (hcols i i.property)
  have hpE (p : Fin 2 → K) (hp0 : p ≠ 0) : E *ᵥ p ≠ 0 := by
    intro hz
    have hh := congrArg (fun v ↦ L *ᵥ v) hz
    rw [Matrix.mulVec_mulVec, hLE, Matrix.one_mulVec, Matrix.mulVec_zero] at hh
    exact hp0 hh
  have hcol (p : Fin 2 → K) (hp0 : p ≠ 0) :
      (G.toFinset.filter fun i ↦ X i ∈ fixedColumnSpace p).card ≤ 2 := by
    have hb := hclass (E *ᵥ p) (hpE p hp0)
    have hh : {i ∈ G | X i ∈ fixedColumnSpace p} ⊆
        {i ∈ G | alg.U i ∈ fixedColumnSpace (Q := Q) (E *ᵥ p)} := by
      rintro i ⟨hi, v, hv⟩
      change vecMulVec p v = X i at hv
      refine ⟨hi, v, ?_⟩
      change vecMulVec (E *ᵥ p) v = alg.U i
      rw [← Matrix.mul_vecMulVec, hv, hU ⟨i, hi⟩]
    have he : (G.toFinset.filter fun i ↦ X i ∈ fixedColumnSpace p).card =
        {i ∈ G | X i ∈ fixedColumnSpace p}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp
    rw [he]
    exact (Set.ncard_le_ncard hh).trans hb
  have hrow (q : Q → K) (hq0 : q ≠ 0) :
      (G.toFinset.filter fun i ↦ (X i).transpose ∈ fixedColumnSpace q).card ≤ 2 := by
    let J := {i ∈ G | (X i).transpose ∈ fixedColumnSpace (Q := Fin 2) q}
    have hrows (i : I) (hi : i ∈ J) :
        alg.U i ∈ matricesInto (S := P) (Submodule.span K {q}) := by
      obtain ⟨v, hv⟩ := hi.2
      change vecMulVec q v = (X i).transpose at hv
      apply (transpose_mem_matricesInto_span_iff q (alg.U i).transpose).mpr
      refine ⟨E *ᵥ v, ?_⟩
      change vecMulVec q (E *ᵥ v) = (alg.U i).transpose
      rw [← hU ⟨i, hi.1⟩, transpose_mul, ← hv, vecMulVec_mul, vecMul_transpose]
    have hb := alg.proper_column_fixed_row_card_le_two hp hq hs hl F
      (by omega) J (fun i hi ↦ hcols i hi.1) q hq0 hrows
    have he : (G.toFinset.filter fun i ↦ (X i).transpose ∈ fixedColumnSpace q).card = J.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp [J]
    rwa [he]
  have hspread (a : K) (p : Fin 2 → K) (hp0 : p ≠ 0) :
      ¬ (∀ i ∈ G.toFinset, t i ≠ a → X i ∈ fixedColumnSpace p) := by
    intro h
    apply alg.supported_test_not_small_fixed_column G (D - a • C) (hDC a)
      (T.sub_mem hD (T.smul_mem a hC)) (E *ᵥ p) (hpE p hp0)
      (by have hb := hclass (E *ᵥ p) (hpE p hp0); rw [hq]; omega)
    intro i hi hn
    have hti : t i ≠ a := by
      intro he
      have he' : alg.toCoefficients.gamma D i = a * c i := (div_eq_iff (hc ⟨i, hi⟩)).mp he
      apply hn
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c, he', sub_self]
    obtain ⟨v, hv⟩ := h i (by simpa using hi) hti
    change vecMulVec p v = X i at hv
    refine ⟨v, ?_⟩
    change vecMulVec (E *ᵥ p) v = alg.U i
    rw [← Matrix.mul_vecMulVec, hv, hU ⟨i, hi⟩]
  have hVlo := alg.supportedTestImage_mass G
  rw [hR, hq] at hVlo
  have hVhi := alg.rotate.finrank_span_coefficients_le_ncard G
  change finrank K (Submodule.span K (alg.V '' G)) ≤ G.ncard at hVhi
  have hVlt : finrank K (Submodule.span K (alg.V '' G)) < G.ncard := by
    by_contra! he
    have heq := Nat.le_antisymm hVhi he
    have hVi : LinearIndependent K (fun i : G ↦ alg.V i) := by
      apply linearIndependent_iff_card_eq_finrank_span.mpr
      rw [← Set.image_eq_range, Set.fintypeCard_eq_ncard]
      change G.ncard = finrank K (Submodule.span K (alg.V '' G))
      exact heq.symm
    have hz := alg.operator_relation_zero_of_independent_second G C D hC hD L H hLD hVi
    have hres (i : I) (hi : i ∈ G.toFinset) : (t i • 1 - H) * X i = 0 := by
      have hh := congrArg (fun A : Matrix (Fin 2) Q K ↦ (c i)⁻¹ • A)
        (hz ⟨i, by simpa using hi⟩)
      change (c i)⁻¹ • (alg.toCoefficients.gamma D i • X i - c i • (H * X i)) = (c i)⁻¹ • 0 at hh
      have hci : c i ≠ 0 := hc ⟨i, by simpa using hi⟩
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ hci,
        one_smul, smul_zero] at hh
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      simpa only [t, div_eq_mul_inv, mul_comm] using hh
    have hb := zero_resolvent_card_le_four G.toFinset H hH X t hres hcol
    rw [Set.toFinset_card, Set.fintypeCard_eq_ncard] at hb
    omega
  have hseven : G.ncard = 7 := by omega
  have hcorank : finrank K (Submodule.span K (alg.V '' G)) + 1 = G.ncard := by omega
  obtain ⟨w, hw0, hw, A, hres⟩ := alg.supported_slice_resolvent_relation G C D hC hD L H hLD hcorank hc
  have hAlo : 2 ≤ A.rank := by
    apply twoDimensional_resolvent_rank_ge_two G.toFinset
      (by rw [Set.toFinset_card, Set.fintypeCard_eq_ncard, hseven]) H hH X t
      (fun i ↦ if hi : i ∈ G then w ⟨i, hi⟩ / c i else 0) A
      _ hcol hrow hspread
    intro i hi
    have hiG : i ∈ G := by simpa using hi
    simpa only [dite_eq_left hiG] using hres (⟨i, hiG⟩ : G)
  have hAhi := A.rank_le_card_height
  have hA2 : A.rank = 2 := by simp only [Fintype.card_fin] at hAhi; omega
  obtain ⟨lam, mu, _, hCH, hrlam, hrmu⟩ := exists_twoDimensional_resolvent_roots H hH
  have hz : ∑ i : G, w i • alg.V i = 0 := by
    change w ∈ (Fintype.linearCombination K (fun i : G ↦ alg.V i)).ker
    rw [hw]
    exact Submodule.subset_span (Set.mem_singleton w)
  exact hmin.resolvent_rank_two_impossible G E L hLE (fun i ↦ X i) (fun i ↦ (hU i).symm)
    H A lam mu (fun i ↦ c i) (fun i ↦ t i) w hc hw0 (by
      have hl : H - lam • 1 = -(lam • 1 - H) := by rw [neg_sub]
      have hm : H - mu • 1 = -(mu • 1 - H) := by rw [neg_sub]
      rw [hl, hm, neg_mul_neg]
      exact hCH) hres hz hA2
    hrlam.le hrmu.le

end MMRank.ExactAlgorithm
