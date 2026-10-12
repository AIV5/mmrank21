module

public import MMRank.ConductorComponentWords
public import MMRank.StationaryConductorPlane
public import MMRank.PlaneCapacity

@[expose] public section

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K] [Infinite K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Оболочка любой активной канонической компоненты имеет размерность qa,
где a — ранг ограничения первых форм. Формат333 и длина≤20 не требуются. -/
theorem component_span_finrank [Nonempty Q] (alg : ExactAlgorithm K P Q S I)
    (η : Q → K) (hη : η ≠ 0) (hgen : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (i : I)
    (hi : ∃ w ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)), w i ≠ 0) :
    let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
    let G := coordinateComponent (M * conductor alg.toCoefficients.gamma.range M) i
    finrank K (Submodule.span K (alg.U '' G)) =
      Fintype.card Q * finrank K (coordinateRestriction M G).range := by
  obtain ⟨d, hd, _, hsupp⟩ := exists_conductor_word_support_component
    (alg.toCoefficients.alphaOn (coordinateHyperplane η)) alg.toCoefficients.gamma.range h1 i hi
  have hh := alg.finrank_conductor_support_span η hη hgen ⟨d, (mem_coordinateSection.mp hd).1⟩
  change finrank K (Submodule.span K (alg.U '' {j | d j ≠ 0})) =
    Fintype.card Q * finrank K ((alg.toCoefficients.alphaOn (coordinateHyperplane η)).map
      (LinearMap.mulRight K d)) at hh
  rw [finrank_mul_word_eq_restriction, hsupp] at hh
  exact hh

/-- Активная каноническая компонента с двумерным ограничением первых форм
определяет постоянную плоскость и имеет не более семи индексов. -/
theorem component_restriction_two_plane (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (hgen : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (i : I)
    (hi : ∃ w ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)), w i ≠ 0)
    (ha : finrank K (coordinateRestriction (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (coordinateComponent (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
        conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) i)).range = 2) :
    let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
    let G := coordinateComponent (M * conductor alg.toCoefficients.gamma.range M) i
    ∃ F : Submodule K (P → K), finrank K F = 2 ∧
      (∀ j ∈ G, (alg.U j).transpose ∈ matricesInto (S := Q) F) ∧
      6 ≤ G.ncard ∧ G.ncard ≤ 7 ∧
      finrank K (coordinateSection K alg.toCoefficients.gamma.range G) ≤ 2 := by
  classical
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
  let N := alg.toCoefficients.gamma.range
  let G := coordinateComponent (M * conductor N M) i
  obtain ⟨d, hd, hd0, hdG⟩ := exists_conductor_word_support_component M N h1 i hi
  have hdim : finrank K (M.map (LinearMap.mulRight K d)) = 2 := by
    rw [finrank_mul_word_eq_restriction, hdG]
    exact ha
  obtain ⟨F, hF, hcols, hcore⟩ := alg.conductor_support_stationary_columns η hη hgen
    ⟨d, (mem_coordinateSection.mp hd).1⟩
  change finrank K F = finrank K (M.map (LinearMap.mulRight K d)) at hF
  rw [hdim] at hF
  have hg : ∀ j ∈ G, (alg.U j).transpose ∈ matricesInto (S := Q) F := by
    intro j hj
    exact hcols j (by change j ∈ {j | d j ≠ 0}; rwa [hdG])
  have hb := alg.plane_coordinateSection_capacity hp hq hs hl η hη h1 F hF G hg
  have hcard := alg.finrank_span_coefficients_le_ncard G
  have hmass := alg.component_span_finrank η hη hgen h1 i hi
  dsimp only at hmass
  rw [ha, hq] at hmass
  rw [show finrank K (Submodule.span K (alg.U '' G)) = 6 from hmass] at hcard
  exact ⟨F, hF, hg, hcard, hb.2, hb.1⟩

/-- Каноническая компонента ранга ограничения 2 имеет именно тип (1,2,2).
Точечные слова вне компоненты допускаются; глобальный рост не ограничивается. -/
theorem component_restriction_two_dimensions (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (hgen : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (i : I)
    (hi : ∃ w ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)), w i ≠ 0)
    (ha : finrank K (coordinateRestriction (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (coordinateComponent (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
        conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) i)).range = 2) :
    let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
    let N := alg.toCoefficients.gamma.range
    let D := conductor N M
    let G := coordinateComponent (M * D) i
    finrank K (coordinateSection K D G) = 1 ∧
      finrank K (coordinateSection K (M * D) G) = 2 ∧
      coordinateSection K (M * D) G = coordinateSection K N G ∧
      HasNoPointWords M (coordinateSection K N G) := by
  let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
  let N := alg.toCoefficients.gamma.range
  let D := conductor N M
  let G := coordinateComponent (M * D) i
  obtain ⟨_, _, _, _, _, hcap⟩ := alg.component_restriction_two_plane hp hq hs hl η hη hgen h1 i hi ha
  change finrank K (coordinateSection K N G) ≤ 2 at hcap
  have hle : coordinateSection K (M * D) G ≤ coordinateSection K N G :=
    inf_le_inf_right _ (mul_conductor_le M N)
  have hdimle := Submodule.finrank_mono hle
  obtain ⟨d, hd, hd0, _⟩ := exists_conductor_word_support_component M N h1 i hi
  change d ∈ coordinateSection K D G at hd
  have hpos : 1 ≤ finrank K (coordinateSection K D G) :=
    Submodule.one_le_finrank_iff.mpr (fun hz ↦ hd0 (by simpa only [hz, Submodule.mem_bot] using hd))
  have hcost := saturated_component_connectivity_cost M N i hi
  change finrank K (coordinateRestriction M G).range + finrank K (coordinateSection K D G) ≤
    finrank K (coordinateSection K (M * D) G) + 1 at hcost
  change finrank K (coordinateRestriction M G).range = 2 at ha
  rw [ha] at hcost
  have hd1 : finrank K (coordinateSection K D G) = 1 := by omega
  have he2 : finrank K (coordinateSection K (M * D) G) = 2 := by omega
  refine ⟨hd1, he2, Submodule.eq_of_le_of_finrank_le hle (hcap.trans he2.ge), ?_⟩
  apply hasNoPointWords_of_one_dimensional_conductor_section M N h1 G hd1
  rw [← saturated_coordinateSection_mul M N G (coordinateComponent_stable _ i)]
  exact he2.ge

end MMRank.ExactAlgorithm
