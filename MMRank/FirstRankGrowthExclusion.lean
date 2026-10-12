module

public import MMRank.RegularPencilGrowth
public import MMRank.ComponentStability

@[expose] public section

/-! # Один обмен запрещает рост насыщенного пространства

Единственное отношение соседнего
столбца выделяет простую пару; один её коэффициент уменьшает первую
ранговую массу. Перенос атомов и второй смешанный столбец не нужны.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

section AlgClosed
variable [IsAlgClosed K] [Nonempty Q]

/-- Активный блок с двумерным ограничением несовместим с минимумом
первой ранговой суммы. Требуется только одно отношение вторых матриц. -/
theorem IsFirstRankMinimal.no_restriction_two
    {alg : ExactAlgorithm K P Q S I} (hmin : alg.IsFirstRankMinimal)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (hcol : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (i : I)
    (hi : ∃ w ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range
        (alg.toCoefficients.alphaOn (coordinateHyperplane η)), w i ≠ 0)
    (ha : finrank K (coordinateRestriction (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (coordinateComponent (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
        conductor alg.toCoefficients.gamma.range
          (alg.toCoefficients.alphaOn (coordinateHyperplane η))) i)).range = 2) : False := by
  let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
  let G := coordinateComponent (M * conductor alg.toCoefficients.gamma.range M) i
  obtain ⟨F, hF, hcols, hlo, hhi, _⟩ :=
    alg.component_restriction_two_plane hp hq hs hl η hη hcol h1 i hi ha
  obtain ⟨hT, _, hR, hreg⟩ :=
    alg.component_restriction_two_test_geometry hp hq hs hl η hη hcol h1 i hi ha
  have hno := (alg.component_restriction_two_dimensions hp hq hs hl η hη hcol h1 i hi ha).2.2.2
  have hclass (p : P → K) (hp0 : p ≠ 0) :
      {j ∈ G | alg.U j ∈ fixedColumnSpace (Q := Q) p}.ncard ≤ 2 := by
    let H := {j ∈ G | alg.U j ∈ fixedColumnSpace (Q := Q) p}
    have hnH : HasNoPointWords M (coordinateSection K alg.toCoefficients.gamma.range H) := by
      apply hno.mono
      intro w hw
      exact mem_coordinateSection.mpr ⟨hw.1, fun j hj ↦ hw.2 j (fun h ↦ hj h.1)⟩
    exact alg.point_free_fixedColumn_card_le_two hp hq hs hl η hη h1 H p hp0
      (Submodule.span_le.mpr (by rintro _ ⟨j, hj, rfl⟩; exact hj.2)) hnH
  obtain ⟨d, hd, _, hdG⟩ := exists_conductor_word_support_component M alg.toCoefficients.gamma.range h1 i hi
  obtain ⟨C, hC⟩ := conductor_le_of_one_mem _ _ h1 hd.1
  have hCG : C ∈ alg.toCoefficients.supportedTests G := by
    rw [Coefficients.mem_supportedTests, hC]
    exact hd.2
  have hγ (j : G) : ∃ C ∈ alg.toCoefficients.supportedTests G,
      alg.toCoefficients.gamma C j ≠ 0 := by
    refine ⟨C, hCG, ?_⟩
    rw [hC]
    exact (show j.val ∈ {j | d j ≠ 0} from by rw [hdG]; exact j.property)
  exact hmin.no_regular_plane hp hq hs hl G F hF hcols hlo hhi hT hR hreg hγ hclass

/-- Рост на единицу создаёт запрещённый двумерный активный блок. -/
theorem IsFirstRankMinimal.growth_one_impossible
    {alg : ExactAlgorithm K P Q S I} (hmin : alg.IsFirstRankMinimal)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (hcol : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hg : finrank K (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
        conductor alg.toCoefficients.gamma.range
          (alg.toCoefficients.alphaOn (coordinateHyperplane η))) =
      finrank K (conductor alg.toCoefficients.gamma.range
        (alg.toCoefficients.alphaOn (coordinateHyperplane η))) + 1) : False := by
  obtain ⟨i, hi, ha⟩ := exists_restriction_two_of_growth_one
    (alg.toCoefficients.alphaOn (coordinateHyperplane η)) alg.toCoefficients.gamma.range h1 hg
  exact hmin.no_restriction_two hp hq hs hl η hη hcol h1 i hi ha

end AlgClosed
end MMRank.ExactAlgorithm
