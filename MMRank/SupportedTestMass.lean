import MMRank.SupportedTestParameters

/-! # Ранговый бюджет всего пространства поддержанных тестов -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Вторая циклическая форма точности восстанавливает AC по носителю γ(C). -/
theorem left_mul_mem_span_of_gamma_supported (alg : ExactAlgorithm K P Q S I)
    (G : Set I) (C : Matrix P S K)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma C i = 0) (A : Matrix Q P K) :
    A * C ∈ Submodule.span K (alg.V '' G) := by
  classical
  have he := alg.rotate.rotate.exact_formula C A
  change A * C = ∑ i, (alg.toCoefficients.gamma C i * alg.toCoefficients.alpha A i) • alg.V i at he
  rw [he]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i ∈ G
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · simp [hG i hi]

/-- Все матрицы со строками из пространства тестовых параметров
лежат в оболочке соседних Vᵢ. Не требуется коллинеарности Uᵢ. -/
theorem matricesInto_testParameters_le_span (alg : ExactAlgorithm K P Q S I)
    (p : P → K) (hp : p ≠ 0) (G : Set I) :
    matricesInto (S := Q) (alg.toCoefficients.supportedTestParameters p G) ≤
      Submodule.span K (alg.V '' G) := by
  classical
  have hsimple (s : alg.toCoefficients.supportedTestParameters p G) (y : Q → K) :
      vecMulVec y s.val ∈ Submodule.span K (alg.V '' G) := by
    obtain ⟨A, hA⟩ := exists_mulVec_eq p hp y
    have hh := alg.left_mul_mem_span_of_gamma_supported G (vecMulVec p s.val)
      ((Coefficients.mem_supportedTestParameters _ _ _ _).mp s.property) A
    rwa [mul_vecMulVec, hA] at hh
  rintro _ ⟨b, rfl⟩
  have he : rowsInclusion (S := Q) (alg.toCoefficients.supportedTestParameters p G) b =
      ∑ q, vecMulVec (Pi.single q 1) (b q).val := by
    ext i j
    change (b i).val j = (∑ q, vecMulVec (Pi.single q 1) (b q).val) i j
    simp [Matrix.sum_apply, vecMulVec, Pi.single_apply]
  rw [he]
  exact Submodule.sum_mem _ (fun q _ ↦ hsimple (b q) _)

/-- Внутренние члены оплачивают q раз размерность всех тестовых параметров. -/
theorem testParameter_mass_le_card (alg : ExactAlgorithm K P Q S I)
    (p : P → K) (hp : p ≠ 0) (G : Set I) :
    Fintype.card Q * finrank K (alg.toCoefficients.supportedTestParameters p G) ≤ G.ncard := by
  have hh := Submodule.finrank_mono (alg.matricesInto_testParameters_le_span p hp G)
  rw [finrank_matricesInto] at hh
  exact hh.trans (alg.rotate.finrank_span_coefficients_le_ncard G)

/-- Бюджет qδ≤|G| для фактического координатного сечения imγ на G. -/
theorem supportedTest_mass_le_card [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (p : P → K) (hp : p ≠ 0) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p) :
    Fintype.card Q * finrank K (coordinateSection K alg.toCoefficients.gamma.range G) ≤ G.ncard := by
  rw [← alg.finrank_supportedTestParameters p hp G hspan]
  exact alg.testParameter_mass_le_card p hp G

end MMRank.ExactAlgorithm
