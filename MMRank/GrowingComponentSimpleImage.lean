module

public import MMRank.ConductorTestGeometry
public import MMRank.GrowingComponentPlane
public import MMRank.PhysicalAtomFullClasses

@[expose] public section

/-! # Простой тест в сингулярном пространстве поддержанных тестов -/

namespace MMRank
open Matrix Module

/-- Одномерное семейство простых пар с ненулевыми вторыми множителями
имеет общий ненулевой нуль, если первые формы действуют на пространстве
размерности хотя бы два. -/
theorem exists_common_kernel_of_smulRight_span_le_one
    {K X Y I : Type*} [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (a : I → X →ₗ[K] K) (b : I → Y)
    (hX : 2 ≤ finrank K X)
    (hd : finrank K (Submodule.span K (Set.range (fun i ↦ (a i).smulRight (b i)))) ≤ 1)
    (hb : ∀ i, b i ≠ 0) :
    ∃ x : X, x ≠ 0 ∧ ∀ i, a i x = 0 := by
  classical
  by_cases hn : ∃ j y, a j y ≠ 0
  · obtain ⟨j, y, hy⟩ := hn
    have hk : (a j).ker ≠ ⊥ := by
      intro hz
      have hh := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hz)
      rw [Module.finrank_self] at hh
      omega
    obtain ⟨x, hx, hx0⟩ := (a j).ker.ne_bot_iff.mp hk
    refine ⟨x, hx0, fun i ↦ ?_⟩
    have he := linearForms_collinear_of_smulRight_span_le_one a b hd i j (hb i) (hb j) x y
    rw [show a j x = 0 from hx, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hy
  · have ht : (⊤ : Submodule K X) ≠ ⊥ := by
      intro hz
      have hh : finrank K X = 0 := by
        simpa using congrArg (fun U : Submodule K X ↦ finrank K U) hz
      omega
    obtain ⟨x, _, hx0⟩ := (⊤ : Submodule K X).ne_bot_iff.mp ht
    exact ⟨x, hx0, fun i ↦ not_ne_iff.mp (fun hi ↦ hn ⟨i, x, hi⟩)⟩

namespace ExactAlgorithm
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Семь индексов не поддерживают двумерное неточечное пространство
тестов с одномерным общим строковым образом и колонковой размерностью≥2.
Нормировка нужна только для превращения минимального теста в точечное слово. -/
theorem supportedTestImage_ne_one_of_two_dimensions
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (G : Set I) (hc : G.ncard ≤ 7)
    (hT : 2 ≤ finrank K (alg.toCoefficients.supportedTests G))
    (hcols : 2 ≤ finrank K (matrixColumnSpan (alg.toCoefficients.supportedTests G)))
    (hn : HasNoPointWords (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (coordinateSection K alg.toCoefficients.gamma.range G)) :
    finrank K (alg.toCoefficients.supportedTestImage G) ≠ 1 := by
  classical
  let T := alg.toCoefficients.supportedTests G
  let H := alg.toCoefficients.supportedTestImage G
  intro hH
  change finrank K H = 1 at hH
  have hH0 : H ≠ ⊥ := by intro hh; rw [hh, finrank_bot] at hH; omega
  obtain ⟨s, hsH, hs0⟩ := H.ne_bot_iff.mp hH0
  have hHs := eq_span_singleton_of_mem_of_finrank_eq_one hH hsH hs0
  let Good : Set I := {i | i ∈ G ∧ alg.V i ∈ matricesInto (S := Q) H}
  let Bad : Set I := {i | i ∈ G ∧ alg.V i ∉ matricesInto (S := Q) H}
  have hg : Good.ncard ≤ 3 := by
    apply alg.rotate.row_class_card_le_three hq hs hp hl s hs0 Good
    intro i hi
    rw [← hHs]
    exact hi.2
  have hb := alg.projectedTestPair_budget G H le_rfl
  rw [hq] at hb
  have hproj : finrank K (Submodule.span K (alg.toCoefficients.projectedTestPair G H '' G)) ≤ 1 := by
    omega
  let f (i : Bad) : T →ₗ[K] K :=
    (LinearMap.proj i.val).comp (alg.toCoefficients.gamma.domRestrict T)
  let v (i : Bad) := (matricesInto (S := Q) H).mkQ (alg.V i)
  have he (i : Bad) : (f i).smulRight (v i) = alg.toCoefficients.projectedTestPair G H i := by
    ext C
    exact (map_smul (matricesInto (S := Q) H).mkQ _ _).symm
  have hd : finrank K (Submodule.span K (Set.range (fun i : Bad ↦ (f i).smulRight (v i)))) ≤ 1 := by
    apply le_trans (Submodule.finrank_mono ?_) hproj
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (f i).smulRight (v i) ∈ Submodule.span K (alg.toCoefficients.projectedTestPair G H '' G)
    rw [he i]
    exact Submodule.subset_span ⟨i.val, i.property.1, rfl⟩
  obtain ⟨C, hC0, hCbad⟩ := exists_common_kernel_of_smulRight_span_le_one f v hT hd
    (fun i hz ↦ i.property.2 ((Submodule.Quotient.mk_eq_zero _).mp hz))
  have hCr : C.val.rank ≤ 1 := by
    have hh := Submodule.finrank_mono
      (le_iSup (fun D : T ↦ D.val.vecMulLinear.range) C)
    change finrank K C.val.vecMulLinear.range ≤ finrank K H at hh
    rwa [hH, ← matrix_rank_eq_finrank_rowRange] at hh
  obtain ⟨p, t, hpt⟩ := exists_vecMulVec_of_rank_le_one C.val hCr
  have hCval : C.val ≠ 0 := fun hz ↦ hC0 (Subtype.ext hz)
  have hp0 : p ≠ 0 := by intro hz; exact hCval (by rw [← hpt, hz]; simp)
  have ht0 : t ≠ 0 := by
    intro hz
    exact hCval (hpt.symm.trans ((outerProduct_eq_zero_iff p t).mpr (Or.inr hz)))
  let J : Set I := {i | alg.toCoefficients.gamma (vecMulVec p t) i ≠ 0}
  have hJG : J ⊆ Good := by
    intro i hi
    have hiG : i ∈ G := by
      by_contra hiG
      exact hi (by rw [hpt]; exact (Coefficients.mem_supportedTests _ _ _).mp C.property i hiG)
    refine ⟨hiG, ?_⟩
    by_contra hVi
    exact hi (by rw [hpt]; exact hCbad ⟨i, hiG, hVi⟩)
  have hlo := alg.card_le_of_gamma_supported_outer J p hp0 t ht0
    (fun i hi ↦ not_ne_iff.mp hi)
  have hhi := (Set.ncard_le_ncard hJG).trans hg
  have hcard : J.ncard = Fintype.card Q := by rw [hq] at hlo ⊢; omega
  let atom : PhysicalAtom alg := ⟨p, t, hp0, ht0, hcard⟩
  apply hn _ ?_ (atom.isPointWord η hη h1)
  refine mem_coordinateSection.mpr ⟨⟨atom.test, rfl⟩, ?_⟩
  intro i hi
  exact not_ne_iff.mp (fun hz ↦ hi (hJG hz).1)

/-- Общий образ канонической компоненты ранга ограничения два двумерен;
общность направления для этого перехода больше не требуется. -/
theorem component_restriction_two_simple_testImage [Infinite K]
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (hcol : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (i : I)
    (hi : ∃ w ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)), w i ≠ 0)
    (ha : finrank K (coordinateRestriction (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (coordinateComponent (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
        conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) i)).range = 2) :
    let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
    let G := coordinateComponent (M * conductor alg.toCoefficients.gamma.range M) i
    finrank K (alg.toCoefficients.supportedTestImage G) = 2 := by
  classical
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
  let N := alg.toCoefficients.gamma.range
  let G := coordinateComponent (M * conductor N M) i
  obtain ⟨F, hF, hFG, _, hc, _⟩ :=
    alg.component_restriction_two_plane hp hq hs hl η hη hcol h1 i hi ha
  obtain ⟨_, hE, heN, hn⟩ :=
    alg.component_restriction_two_dimensions hp hq hs hl η hη hcol h1 i hi ha
  have hT : finrank K (alg.toCoefficients.supportedTests G) = 2 := by
    rw [(alg.supportedTestsEquiv G).finrank_eq, ← heN]
    exact hE
  obtain ⟨d, hd, _, hdG⟩ := exists_conductor_word_support_component M N h1 i hi
  have hcols := alg.conductor_rank_le_supportedTests_columnSpan η hη ⟨d, hd.1⟩
  change finrank K (M.map (LinearMap.mulRight K d)) ≤
    finrank K (matrixColumnSpan (alg.toCoefficients.supportedTests {j | d j ≠ 0})) at hcols
  rw [finrank_mul_word_eq_restriction, hdG, ha] at hcols
  have hne := alg.supportedTestImage_ne_one_of_two_dimensions hp hq hs hl η hη h1 G hc
    hT.ge hcols hn
  have hcap := alg.supportedTests_capacity F G hFG
  rw [hF, hT] at hcap
  have hbud := alg.supportedTests_internal_budget_of_hyperplane G η hη h1
  rw [hT, hq] at hbud
  change finrank K (alg.toCoefficients.supportedTestImage G) = 2
  change G.ncard ≤ 7 at hc
  change 2 ≤ 2 * finrank K (alg.toCoefficients.supportedTestImage G) at hcap
  change 2 + 3 * finrank K (alg.toCoefficients.supportedTestImage G) ≤
    G.ncard + finrank K (alg.toCoefficients.supportedTestImage G) at hbud
  omega

end ExactAlgorithm
end MMRank
