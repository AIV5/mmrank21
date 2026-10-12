module

public import MMRank.PhysicalAtomFamilies
public import Mathlib.Data.Set.Card.Arithmetic

@[expose] public section

/-! # Точный размер объединения физических атомов -/
namespace MMRank.ExactAlgorithm.PhysicalAtom
open Matrix
variable {K P Q S I J : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Fintype J]
  {alg : ExactAlgorithm K P Q S I}

/-- Различные физические атомы дают ровно |J|·|Q| индексов ранга1
в обоих соседних столбцах. Нормировка и формат333 не нужны. -/
theorem union_rank_one (a : J → PhysicalAtom alg)
    (hd : Function.Injective (fun j ↦ (a j).support)) :
    ∃ G : Finset I, G.card = Fintype.card J * Fintype.card Q ∧
      (∀ i, i ∈ G ↔ ∃ j, i ∈ (a j).support) ∧
      ∀ i ∈ G, (alg.U i).rank = 1 ∧ (alg.V i).rank = 1 := by
  classical
  have hdis : Pairwise (fun j k ↦ Disjoint (a j).support (a k).support) := by
    intro j k hjk
    exact ((a j).support_eq_or_disjoint (a k)).resolve_left (fun he ↦ hjk (hd he))
  let G := (⋃ j, (a j).support).toFinset
  have hG (i : I) : i ∈ G ↔ ∃ j, i ∈ (a j).support := by simp [G]
  refine ⟨G, ?_, hG, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card',
      Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) hdis]
    simp [show ∀ j, (a j).support.ncard = Fintype.card Q from fun j ↦ (a j).card_support,
      finsum_eq_sum_of_fintype]
  · intro i hi
    obtain ⟨j, hj⟩ := (hG i).mp hi
    exact (a j).ranks_eq_one hj

end MMRank.ExactAlgorithm.PhysicalAtom
