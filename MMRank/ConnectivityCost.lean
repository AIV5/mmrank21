import MMRank.ConnectedTensorDimension
import MMRank.ProductTensorEmbedding
import Mathlib.Algebra.DirectSum.Module

/-! # Локальная и суммарная цена связности насыщенной пары

Для D=(N:M), E=MD тензорная лемма оценивает размерность ограничения M
на каждую компоненту. Суммарная оценка при 1∈M учитывает все различные
канонические блоки ровно по одному; нулевые блоки дают нулевой вклад.
-/

namespace MMRank

open Module

set_option backward.isDefEq.respectTransparency false

section DirectSum

variable {K V β : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype β]

/-- Размерности конечного независимого семейства подпространств суммируются.
Конечномерность всего объемлющего пространства не требуется. -/
theorem finrank_iSup_eq_sum_of_iSupIndep (p : β → Submodule K V)
    [∀ b, FiniteDimensional K (p b)] (hp : iSupIndep p) :
    finrank K ↥(⨆ b, p b) = ∑ b, finrank K (p b) := by
  classical
  have hi : Function.Injective (DirectSum.coeLinearMap p) := hp.dfinsupp_lsum_injective
  have hh := LinearMap.finrank_range_of_inj hi
  rw [DirectSum.range_coeLinearMap, Module.finrank_directSum] at hh
  exact hh

end DirectSum

variable {K ι : Type*} [Field K] [Finite ι]

/-- Цена связности активной насыщенной компоненты, в аддитивной форме.
Единица в M не нужна. -/
theorem saturated_component_connectivity_cost (M N : Submodule K (ι → K)) (i : ι)
    (hi : ∃ x ∈ M * conductor N M, x i ≠ 0) :
    finrank K (coordinateRestriction M (coordinateComponent (M * conductor N M) i)).range +
      finrank K (coordinateSection K (conductor N M) (coordinateComponent (M * conductor N M) i)) ≤
      finrank K (coordinateSection K (M * conductor N M) (coordinateComponent (M * conductor N M) i)) + 1 := by
  obtain ⟨hc, hn, ht, hm, hd⟩ := saturated_component_tensor_data M N i hi
  have hh := finrank_factors_le_tensor_span_add_one_of_finite
    (coordinateEval M) (coordinateEval (conductor N M))
    (coordinateComponent (M * conductor N M) i) (Set.toFinite _) hc hn
  change finrank K (coordinateEvalSpan M _) + finrank K (coordinateEvalSpan (conductor N M) _) ≤
    finrank K (Submodule.span K (coordinateProductTensor M (conductor N M) '' _)) + 1 at hh
  rw [ht, hm, hd] at hh
  exact hh

/-- Цена связности с натуральными разностями. Нулевые одноточечные блоки
тоже допускаются: их вклад слева равен нулю. -/
theorem saturated_component_connectivity_cost_sub (M N : Submodule K (ι → K))
    (i : ι) :
    finrank K (coordinateRestriction M (coordinateComponent (M * conductor N M) i)).range - 1 ≤
      finrank K (coordinateSection K (M * conductor N M) (coordinateComponent (M * conductor N M) i)) -
      finrank K (coordinateSection K (conductor N M) (coordinateComponent (M * conductor N M) i)) := by
  classical
  by_cases hi : ∃ x ∈ M * conductor N M, x i ≠ 0
  · have hh := saturated_component_connectivity_cost M N i hi
    omega
  · have hz : ∀ x ∈ M * conductor N M, x i = 0 := by simpa using hi
    have he := coordinateComponent_eq_singleton_of_eval_zero (M * conductor N M) i hz
    have hd : finrank K (coordinateRestriction M (coordinateComponent (M * conductor N M) i)).range ≤ 1 := by
      rw [← finrank_coordinateEvalSpan, he]
      change finrank K (Submodule.span K (coordinateEval M '' {i})) ≤ 1
      rw [Set.image_singleton]
      exact finrank_span_le_card ({coordinateEval M i} : Set (Module.Dual K M))
    omega

/-- Сумма размерностей сечений канонического разложения без повторения блоков. -/
theorem sum_finrank_coordinateComponents (N : Submodule K (ι → K))
    [Fintype (Set.range (coordinateComponent N))] :
    (∑ c : Set.range (coordinateComponent N), finrank K (coordinateSection K N c.val)) =
      finrank K N := by
  have hh := finrank_iSup_eq_sum_of_iSupIndep
    (fun c : Set.range (coordinateComponent N) ↦ coordinateSection K N c.val)
    (coordinateComponents_direct N).1
  rw [(coordinateComponents_direct N).2] at hh
  exact hh.symm

/-- Глобальная цена связности: малый прирост ограничивает сумму проективных
размерностей ограничений M. Нулевые блоки дают нулевые слагаемые.
Здесь единица нужна для D⊆E и суммирования обычных разностей. -/
theorem saturated_total_connectivity_cost (M N : Submodule K (ι → K))
    (h1 : (1 : ι → K) ∈ M)
    [Fintype (Set.range (coordinateComponent (M * conductor N M)))] :
    (∑ c : Set.range (coordinateComponent (M * conductor N M)),
      (finrank K (coordinateRestriction M c.val).range - 1)) ≤
      finrank K (M * conductor N M) - finrank K (conductor N M) := by
  classical
  let D := conductor N M
  let E := M * D
  let β := Set.range (coordinateComponent E)
  have hd : iSupIndep (fun c : β ↦ coordinateSection K D c.val) :=
    coordinateSections_iSupIndep D _ (coordinateBlocks_pairwise_disjoint E)
  have hsumd : (⨆ c : β, coordinateSection K D c.val) = D := by
    apply coordinateSections_iSup_eq D _ (coordinateBlocks_pairwise_disjoint E)
    · intro i
      exact ⟨⟨coordinateComponent E i, ⟨i, rfl⟩⟩, mem_coordinateComponent_self E i⟩
    · rintro ⟨_, i, rfl⟩
      exact (saturated_coordinateProjection_stable_iff M N _).mpr
        (coordinateComponent_stable E i)
  have hdimd := finrank_iSup_eq_sum_of_iSupIndep (fun c : β ↦ coordinateSection K D c.val) hd
  rw [hsumd] at hdimd
  have hdime := sum_finrank_coordinateComponents E
  have hle : ∀ c : β, finrank K (coordinateSection K D c.val) ≤
      finrank K (coordinateSection K E c.val) := by
    intro c
    exact Submodule.finrank_mono (inf_le_inf_right _ (le_mul_of_one_mem M D h1))
  have hc : ∀ c : β, finrank K (coordinateRestriction M c.val).range - 1 +
      finrank K (coordinateSection K D c.val) ≤ finrank K (coordinateSection K E c.val) := by
    rintro ⟨_, i, rfl⟩
    have hh := saturated_component_connectivity_cost_sub M N i
    have hh' := hle ⟨coordinateComponent E i, ⟨i, rfl⟩⟩
    dsimp only [D, E] at hh' ⊢
    omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hc c)
  rw [Finset.sum_add_distrib, ← hdimd, hdime] at hh
  change (∑ c : β, (finrank K (coordinateRestriction M c.val).range - 1)) ≤
    finrank K E - finrank K D
  omega

/-- Размерность ограничения на любой блок ограничена общим приростом плюс один. -/
theorem saturated_component_restriction_finrank_le (M N : Submodule K (ι → K))
    (h1 : (1 : ι → K) ∈ M) (i : ι) :
    finrank K (coordinateRestriction M (coordinateComponent (M * conductor N M) i)).range ≤
      finrank K (M * conductor N M) - finrank K (conductor N M) + 1 := by
  classical
  let E := M * conductor N M
  let β := Set.range (coordinateComponent E)
  let : Fintype β := Fintype.ofFinite β
  let c : β := ⟨coordinateComponent E i, ⟨i, rfl⟩⟩
  have hs := Finset.single_le_sum
    (f := fun c : β ↦ finrank K (coordinateRestriction M c.val).range - 1)
    (fun c _ ↦ Nat.zero_le _) (Finset.mem_univ c)
  have ht := saturated_total_connectivity_cost M N h1
  have hh := hs.trans ht
  change finrank K (coordinateRestriction M (coordinateComponent E i)).range - 1 ≤ _ at hh
  dsimp only [E] at hh
  omega

/-- Число различных блоков с ограничением размерности хотя бы два
не превосходит общего прироста. -/
theorem saturated_nontrivial_components_card_le (M N : Submodule K (ι → K))
    (h1 : (1 : ι → K) ∈ M)
    [Fintype (Set.range (coordinateComponent (M * conductor N M)))] :
    (Finset.univ.filter (fun c : Set.range (coordinateComponent (M * conductor N M)) ↦
      2 ≤ finrank K (coordinateRestriction M c.val).range)).card ≤
      finrank K (M * conductor N M) - finrank K (conductor N M) := by
  classical
  let β := Set.range (coordinateComponent (M * conductor N M))
  let w := fun c : β ↦ finrank K (coordinateRestriction M c.val).range - 1
  let s := Finset.univ.filter (fun c : β ↦ 2 ≤ finrank K (coordinateRestriction M c.val).range)
  have hs : s.card ≤ ∑ c ∈ s, w c := by
    calc
      s.card = ∑ _c ∈ s, (1 : ℕ) := by simp
      _ ≤ ∑ c ∈ s, w c := by
        apply Finset.sum_le_sum
        intro c hc
        have hh := (Finset.mem_filter.mp hc).2
        dsimp [w]
        omega
  have hle : (∑ c ∈ s, w c) ≤ ∑ c : β, w c := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ ↦ Nat.zero_le _)
  exact (hs.trans hle).trans (saturated_total_connectivity_cost M N h1)

end MMRank
