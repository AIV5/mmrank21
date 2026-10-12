import MMRank.FixedColumnSpace

/-! # Выходной тест и коэффициентная оболочка его носителя -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Точность восстанавливает CB только по индексам носителя γ(C). -/
theorem mul_mem_span_of_gamma_supported (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (C : Matrix P S K)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma C i = 0) (B : Matrix S Q K) :
    C * B ∈ Submodule.span K (alg.U '' G) := by
  classical
  have he := alg.rotate.exact_formula B C
  change C * B = ∑ i, (alg.toCoefficients.beta B i * alg.toCoefficients.gamma C i) • alg.U i at he
  rw [he]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ G
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · simp [hG i hi]

/-- Ненулевой простой тест заставляет поддержанные Uᵢ порождать
все матрицы с тем же первым фактором. -/
theorem fixedColumnSpace_le_span_of_gamma_supported (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0) :
    fixedColumnSpace (Q := Q) p ≤ Submodule.span K (alg.U '' G) := by
  rw [fixedColumnSpace_eq_range_mul p s hs]
  rintro _ ⟨B, rfl⟩
  exact alg.mul_mem_span_of_gamma_supported G _ hG B

theorem finrank_span_coefficients_le_ncard (alg : ExactAlgorithm K P Q S ι) (G : Set ι) :
    finrank K (Submodule.span K (alg.U '' G)) ≤ G.ncard := by
  classical
  have h : finrank K (Submodule.span K (alg.U '' G)) ≤ (alg.U '' G).ncard := by
    simpa only [Set.toFinset_card, Set.fintypeCard_eq_ncard] using
      (finrank_span_le_card (R := K) (alg.U '' G))
  exact h.trans Set.ncard_image_le

/-- Носитель ненулевого простого теста имеет не меньше q индексов. -/
theorem card_le_of_gamma_supported_outer (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0) :
    Fintype.card Q ≤ G.ncard := by
  have h := Submodule.finrank_mono (alg.fixedColumnSpace_le_span_of_gamma_supported G p s hs hG)
  rw [finrank_fixedColumnSpace hp] at h
  exact h.trans (alg.finrank_span_coefficients_le_ncard G)

/-- Если носитель имеет минимальную мощность q, его оболочка в точности
равна пространству p⊗K^Q; общего фактора Uᵢ заранее не предполагается. -/
theorem span_eq_fixedColumnSpace_of_minimal_gamma_support (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (hc : G.ncard = Fintype.card Q) :
    Submodule.span K (alg.U '' G) = fixedColumnSpace (Q := Q) p := by
  have hle := alg.fixedColumnSpace_le_span_of_gamma_supported G p s hs hG
  have hlo := Submodule.finrank_mono hle
  have hhi := alg.finrank_span_coefficients_le_ncard G
  rw [hc, ← finrank_fixedColumnSpace hp] at hhi
  exact (Submodule.eq_of_le_of_finrank_eq hle (Nat.le_antisymm hlo hhi)).symm

end MMRank.ExactAlgorithm
