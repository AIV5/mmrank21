module

public import MMRank.GrowingComponentSimpleImage
public import MMRank.RegularMatrixPencil

@[expose] public section

/-! # Второй совместный образ компоненты (1,2,2) -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Оба совместных носителя и само пространство тестов двумерны;
в исходном физическом пространстве существует тест ранга ровно два.
Это регулярность пучка на его носителях, ещё не его расщепление. -/
theorem component_restriction_two_test_geometry [Infinite K]
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
    let T := alg.toCoefficients.supportedTests G
    finrank K T = 2 ∧ finrank K (matrixColumnSpan T) = 2 ∧
      finrank K (alg.toCoefficients.supportedTestImage G) = 2 ∧ ∃ C ∈ T, C.rank = 2 := by
  classical
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
  let N := alg.toCoefficients.gamma.range
  let G := coordinateComponent (M * conductor N M) i
  let T := alg.toCoefficients.supportedTests G
  have hH : finrank K (alg.toCoefficients.supportedTestImage G) = 2 :=
    alg.component_restriction_two_simple_testImage hp hq hs hl η hη hcol h1 i hi ha
  obtain ⟨F, hF, hFG, _, _, _⟩ :=
    alg.component_restriction_two_plane hp hq hs hl η hη hcol h1 i hi ha
  obtain ⟨_, hE, heN, _⟩ :=
    alg.component_restriction_two_dimensions hp hq hs hl η hη hcol h1 i hi ha
  have hT : finrank K T = 2 := by
    rw [(alg.supportedTestsEquiv G).finrank_eq, ← heN]
    exact hE
  have hcols : matrixColumnSpan T ≤ F := by
    apply iSup_le
    intro C
    exact (mem_matricesInto F _).mp (alg.supportedTests_columns F G hFG C)
  obtain ⟨d, hd, _, hdG⟩ := exists_conductor_word_support_component M N h1 i hi
  have hlo := alg.conductor_rank_le_supportedTests_columnSpan η hη ⟨d, hd.1⟩
  change finrank K (M.map (LinearMap.mulRight K d)) ≤
    finrank K (matrixColumnSpan (alg.toCoefficients.supportedTests {j | d j ≠ 0})) at hlo
  rw [finrank_mul_word_eq_restriction, hdG, ha] at hlo
  have hhi := Submodule.finrank_mono hcols
  rw [hF] at hhi
  have hF2 : finrank K (matrixColumnSpan T) = 2 := Nat.le_antisymm hhi hlo
  have hrow : finrank K (matrixColumnSpan (T.map (transposeLinearEquiv P S K K).toLinearMap)) = 2 := by
    rw [matrixColumnSpan_transpose]
    exact hH
  obtain ⟨C, hC, hC2⟩ := exists_rank_ge_two_of_joint_spans T hF2.ge hrow.ge
  have hCr : C.vecMulLinear.range ≤ alg.toCoefficients.supportedTestImage G :=
    le_iSup (fun D : T ↦ D.val.vecMulLinear.range) ⟨C, hC⟩
  have hbound := Submodule.finrank_mono hCr
  rw [hH, ← matrix_rank_eq_finrank_rowRange] at hbound
  exact ⟨hT, hF2, hH, C, hC, Nat.le_antisymm hbound hC2⟩

end MMRank.ExactAlgorithm
