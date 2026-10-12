module

public import MMRank.RectangularTestChart
public import MMRank.ScalarProductLowerBound

@[expose] public section

namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Nonempty Q]

/-- Поддержанные тесты между двумя плоскостями дают настоящую частичную
формулу2×q на q×2, с независимыми входами и прежними внутренними индексами. -/
theorem exists_supported_twoByTwo_formula_with_chart
    (alg : ExactAlgorithm K P Q S I) (F : Submodule K (P → K)) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F)
    (hF : finrank K F = 2) (hH : finrank K (alg.toCoefficients.supportedTestImage G) = 2) :
    ∃ E : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix P S K,
      Function.Injective E ∧ (∀ C, (E C).rank = C.rank) ∧
    ∃ T : Submodule K (Matrix (Fin 2) (Fin 2) K),
      T.map E = alg.toCoefficients.supportedTests G ∧
      finrank K T = finrank K (alg.toCoefficients.supportedTests G) ∧
    ∃ (a : G → Matrix (Fin 2) Q K →ₗ[K] K) (b : G → Matrix Q (Fin 2) K →ₗ[K] K)
      (c : G → Matrix (Fin 2) (Fin 2) K →ₗ[K] K),
      ∀ C ∈ T, ∀ A B, trace (C * (A * B)) = ∑ i, (a i A * b i B) * c i C := by
  classical
  let T := alg.toCoefficients.supportedTests G
  let H := alg.toCoefficients.supportedTestImage G
  obtain ⟨E, L, R, hE, hTE, _, htrace, hrank⟩ := exists_rectangular_test_chart_rank T F H 2 2 hF hH
    (fun C hC ↦ alg.supportedTests_columns F G hG ⟨C, hC⟩) (by
      intro C hC
      apply (mem_matricesInto H C).mpr
      exact le_iSup (fun D : T ↦ D.val.vecMulLinear.range) ⟨C, hC⟩)
  let a : G → Matrix (Fin 2) Q K →ₗ[K] K := fun i ↦
    (LinearMap.proj i.val).comp (alg.toCoefficients.beta.comp (mulLeftLinearMap Q K R))
  let b : G → Matrix Q (Fin 2) K →ₗ[K] K := fun i ↦
    (LinearMap.proj i.val).comp (alg.toCoefficients.alpha.comp (mulRightLinearMap Q K L))
  let c : G → Matrix (Fin 2) (Fin 2) K →ₗ[K] K := fun i ↦
    (LinearMap.proj i.val).comp (alg.toCoefficients.gamma.comp E)
  refine ⟨E, hE, hrank, T.comap E, ?_, finrank_comap_of_injective_of_le_range E hE T hTE, a, b, c, ?_⟩
  · rw [Submodule.map_comap_eq, inf_eq_right.mpr hTE]
  intro C hC A B
  have hz := (Coefficients.mem_supportedTests _ _ _).mp hC
  have hh := alg.trace_identity (B * L) (R * A) (E C)
  have ht := htrace C (A * B).transpose
  rw [transpose_transpose] at ht
  have hleft : trace (E C * (R * A) * (B * L)) = trace (C * (A * B)) := by
    simpa only [Matrix.mul_assoc] using ht
  rw [hleft] at hh
  rw [hh]
  apply Finset.sum_congr_set G _ _
  · intro i hi
    change (alg.toCoefficients.alpha (B * L) i * alg.toCoefficients.beta (R * A) i) *
      alg.toCoefficients.gamma (E C) i = _
    change _ = (alg.toCoefficients.beta (R * A) i * alg.toCoefficients.alpha (B * L) i) *
      alg.toCoefficients.gamma (E C) i
    ring
  · intro i hi
    change (alg.toCoefficients.alpha (B * L) i * alg.toCoefficients.beta (R * A) i) *
      alg.toCoefficients.gamma (E C) i = 0
    rw [hz i hi, mul_zero]

/-- Прежняя частичная формула получается забыванием явной модели тестов. -/
theorem exists_supported_twoByTwo_formula
    (alg : ExactAlgorithm K P Q S I) (F : Submodule K (P → K)) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F)
    (hF : finrank K F = 2) (hH : finrank K (alg.toCoefficients.supportedTestImage G) = 2) :
    ∃ T : Submodule K (Matrix (Fin 2) (Fin 2) K),
      finrank K T = finrank K (alg.toCoefficients.supportedTests G) ∧
    ∃ (a : G → Matrix (Fin 2) Q K →ₗ[K] K) (b : G → Matrix Q (Fin 2) K →ₗ[K] K)
      (c : G → Matrix (Fin 2) (Fin 2) K →ₗ[K] K),
      ∀ C ∈ T, ∀ A B, trace (C * (A * B)) = ∑ i, (a i A * b i B) * c i C := by
  obtain ⟨_, _, _, T, _, hd, a, b, c, h⟩ :=
    alg.exists_supported_twoByTwo_formula_with_chart F G hG hF hH
  exact ⟨T, hd, a, b, c, h⟩

/-- Единый бюджет поддержанных тестов
между двумя плоскостями; каждое измерение сверх трёх добавляет один член. -/
theorem supportedTests_dimension_lower
    (alg : ExactAlgorithm K P Q S I) (F : Submodule K (P → K)) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F)
    (hF : finrank K F = 2) (hH : finrank K (alg.toCoefficients.supportedTestImage G) = 2)
    (hT : 3 ≤ finrank K (alg.toCoefficients.supportedTests G)) :
    3 * Fintype.card Q + finrank K (alg.toCoefficients.supportedTests G) ≤ G.ncard + 3 := by
  classical
  obtain ⟨T, hdim, a, b, c, h⟩ := alg.exists_supported_twoByTwo_formula F G hG hF hH
  have hb := partial_twoByTwo_dimension_lower T (by omega) a b c h
  simpa only [hdim, Set.fintypeCard_eq_ncard] using hb

end MMRank.ExactAlgorithm
