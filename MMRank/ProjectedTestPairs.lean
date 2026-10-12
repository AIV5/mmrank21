import MMRank.TestSliceRank

/-! # Бюджет простых пар после факторизации по совместному образу тестов -/

namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Пара из координаты тестового слова и второго коэффициента. -/
def Coefficients.testPair (d : Coefficients K P Q S I) (G : Set I) (i : I) :
    d.supportedTests G →ₗ[K] Matrix Q S K :=
  ((LinearMap.proj i).comp (d.gamma.domRestrict (d.supportedTests G))).smulRight (d.V i)

/-- Та же пара после удаления строк из H. -/
def Coefficients.projectedTestPair (d : Coefficients K P Q S I) (G : Set I)
    (H : Submodule K (S → K)) (i : I) :
    d.supportedTests G →ₗ[K] (Matrix Q S K ⧸ matricesInto (S := Q) H) :=
  (matricesInto (S := Q) H).mkQ.comp (d.testPair G i)

namespace ExactAlgorithm

/-- Полная свёртка тестов лежит в оболочке внутренних простых пар. -/
theorem leftTestSlices_le_testPair_span (alg : ExactAlgorithm K P Q S I) (G : Set I) :
    (leftTestSlices (Q := Q) (alg.toCoefficients.supportedTests G)).range ≤
      Submodule.span K (alg.toCoefficients.testPair G '' G) := by
  classical
  rintro _ ⟨A, rfl⟩
  have he : leftTestSlices (alg.toCoefficients.supportedTests G) A =
      ∑ i : G, alg.toCoefficients.alpha A i • alg.toCoefficients.testPair G i := by
    ext C q s
    have hh := alg.rotate.rotate.exact_formula C.val A
    change A * C.val = ∑ i,
      (alg.toCoefficients.gamma C.val i * alg.toCoefficients.alpha A i) • alg.V i at hh
    have hs : (∑ i, (alg.toCoefficients.gamma C.val i * alg.toCoefficients.alpha A i) • alg.V i) =
        ∑ i : G, (alg.toCoefficients.gamma C.val i * alg.toCoefficients.alpha A i) • alg.V i := by
      apply Finset.sum_congr_set G _ _ (fun _ _ ↦ rfl)
      intro i hi
      rw [(Coefficients.mem_supportedTests _ _ _).mp C.property i hi, zero_mul, zero_smul]
    rw [hs] at hh
    simpa [leftTestSlices, Coefficients.testPair, smul_smul, mul_comm] using
      congrFun (congrFun hh q) s
  rw [he]
  exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i.val, i.property, rfl⟩))

/-- q·dim F независимых свёрток исчезают в факторе по H, если H
содержит совместный образ тестов. Бюджет не требует нормировки или общности. -/
theorem projectedTestPair_budget (alg : ExactAlgorithm K P Q S I)
    (G : Set I) (H : Submodule K (S → K))
    (hH : alg.toCoefficients.supportedTestImage G ≤ H) :
    finrank K (Submodule.span K (alg.toCoefficients.projectedTestPair G H '' G)) +
      Fintype.card Q * finrank K (matrixColumnSpan (alg.toCoefficients.supportedTests G)) ≤
      G.ncard := by
  classical
  let T := alg.toCoefficients.supportedTests G
  let E := Submodule.span K (alg.toCoefficients.testPair G '' G)
  let π : (T →ₗ[K] Matrix Q S K) →ₗ[K]
      (T →ₗ[K] (Matrix Q S K ⧸ matricesInto (S := Q) H)) :=
    LinearMap.llcomp K T _ _ (matricesInto (S := Q) H).mkQ
  have hz : (leftTestSlices (Q := Q) T).range ≤ π.ker := by
    rintro _ ⟨A, rfl⟩
    change π (leftTestSlices T A) = 0
    ext C
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply (mem_matricesInto H _).mpr
    change (A * C.val).vecMulLinear.range ≤ H
    rw [rowLinear_mul, LinearMap.range_comp]
    apply le_trans (Submodule.map_mono le_top)
    rw [Submodule.map_top]
    exact (le_iSup (fun D : T ↦ D.val.vecMulLinear.range) C).trans hH
  have hb := finrank_map_add_le_of_le_ker π E (leftTestSlices (Q := Q) T).range
    (alg.leftTestSlices_le_testPair_span G) hz
  have he : E.map π = Submodule.span K (alg.toCoefficients.projectedTestPair G H '' G) := by
    rw [Submodule.map_span, Set.image_image]
    rfl
  have hd : finrank K E ≤ G.ncard := by
    have hd' : finrank K E ≤ (alg.toCoefficients.testPair G '' G).ncard := by
      simpa only [Set.toFinset_card, Set.fintypeCard_eq_ncard] using
        (finrank_span_le_card (R := K) (alg.toCoefficients.testPair G '' G))
    exact hd'.trans Set.ncard_image_le
  rw [he, finrank_leftTestSlices] at hb
  exact hb.trans hd

end ExactAlgorithm
end MMRank
