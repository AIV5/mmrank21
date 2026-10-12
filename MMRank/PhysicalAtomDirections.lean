module

public import MMRank.PhysicalAtomFamilies
public import MMRank.AtomDirectionBases

@[expose] public section

/-! # Независимость направлений физических атомов -/
namespace MMRank.ExactAlgorithm.PhysicalAtom
open Matrix Module
variable {K P Q S I : Type*} [Field K] [Infinite K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  {alg : ExactAlgorithm K P Q S I}

/-- Любые три различных физических атома333≤20 имеют независимые
первые и последние направления; общей нормировки семейства не требуется. -/
theorem three_directions_linearIndependent (a : Fin 3 → PhysicalAtom alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (hn : alg.toCoefficients.NonzeroTerms)
    (hd : Function.Injective (fun j ↦ (a j).support)) :
    LinearIndependent K (fun j ↦ (a j).first) ∧ LinearIndependent K (fun j ↦ (a j).last) := by
  have hdis : Pairwise (fun j k ↦ Disjoint (a j).support (a k).support) :=
    pairwise_disjoint_support a hd
  have hc (j) : (a j).support.ncard = 3 := (a j).card_support.trans hq
  exact ⟨alg.three_class_directions_linearIndependent_of_nonzero hp hq hs hl (fun i ↦ (hn i).1)
    (fun j ↦ (a j).first) (fun j ↦ (a j).support) hdis hc (fun j _ hi ↦ (a j).U_mem hi),
    alg.rotate.three_row_directions_linearIndependent hq hs hp hl
      (fun i ↦ (hn i).2.1)
      (fun j ↦ (a j).last) (fun j ↦ (a j).support) hdis hc (fun j _ hi ↦ (a j).V_mem hi)⟩

/-- Первые направления любой тройки различных атомов образуют базис P. -/
theorem exists_three_first_basis (a : Fin 3 → PhysicalAtom alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (hn : alg.toCoefficients.NonzeroTerms)
    (hd : Function.Injective (fun j ↦ (a j).support)) :
    ∃ f : Basis (Fin 3) K (P → K), ∀ j, f j = (a j).first := by
  have hi := (three_directions_linearIndependent a hp hq hs hl hn hd).1
  have hspan : Submodule.span K (Set.range (fun j ↦ (a j).first)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hi]
    simp [hp]
  exact ⟨Basis.mk hi hspan.ge, fun j ↦ Basis.mk_apply _ _ j⟩

/-- Последние направления трёх различных атомов порождают всё S. -/
theorem span_three_last_eq_top (a : Fin 3 → PhysicalAtom alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (hn : alg.toCoefficients.NonzeroTerms)
    (hd : Function.Injective (fun j ↦ (a j).support)) :
    Submodule.span K (Set.range (fun j ↦ (a j).last)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card (three_directions_linearIndependent a hp hq hs hl hn hd).2]
  simp [hs]

end MMRank.ExactAlgorithm.PhysicalAtom
