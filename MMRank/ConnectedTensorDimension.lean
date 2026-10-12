import MMRank.TensorRank
import MMRank.MinimalSpanBridge

/-! # Размерностное неравенство для связного семейства простых тензоров

Доказательство увеличивает максимальное допустимое подсемейство минимальным
мостом. Размерность факторов растёт не быстрее размерности тензорной оболочки.
-/

open scoped TensorProduct
open Module

namespace MMRank

set_option backward.isDefEq.respectTransparency false

variable {K ι X Y : Type*} [Field K]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
variable [FiniteDimensional K X] [FiniteDimensional K Y]

/-- Неравенство связности сохраняется при присоединении минимального моста. -/
theorem tensor_dimension_bound_union_of_minimal_bridge
    [DecidableEq ι] (x : ι → X) (y : ι → Y) (a q : Finset ι)
    (ha : finrank K (Submodule.span K (x '' (a : Set ι))) +
      finrank K (Submodule.span K (y '' (a : Set ι))) ≤
      finrank K (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' (a : Set ι))) + 1)
    (hmeet : ¬ Disjoint
      (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' (a : Set ι)))
      (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' (q : Set ι))))
    (hmin : ∀ r ⊂ q, Disjoint
      (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' (a : Set ι)))
      (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' (r : Set ι)))) :
    finrank K (Submodule.span K (x '' ((a ∪ q : Finset ι) : Set ι))) +
      finrank K (Submodule.span K (y '' ((a ∪ q : Finset ι) : Set ι))) ≤
      finrank K (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' ((a ∪ q : Finset ι) : Set ι))) + 1 := by
  classical
  let t := fun i ↦ x i ⊗ₜ[K] y i
  let L := Submodule.span K (t '' (a : Set ι))
  let Q := Submodule.span K (t '' (q : Set ι))
  obtain ⟨hi, c, hc, hw, he⟩ := minimal_span_bridge_on_finset t L q hmeet hmin
  have hmem : Fintype.linearCombination K (fun i : q ↦ t i) c ∈ L := by
    have hh := Submodule.mem_span_singleton_self
      (Fintype.linearCombination K (fun i : q ↦ t i) c) (R := K)
    rw [← he] at hh
    exact hh.1
  have hg := tensor_bridge_factor_growth x y (a : Set ι)
    (fun i : q ↦ x i) (fun i : q ↦ y i) c hc hw hmem
  have hx : Set.range (fun i : q ↦ x i) = x '' (q : Set ι) :=
    (Set.image_eq_range x (q : Set ι)).symm
  have hy : Set.range (fun i : q ↦ y i) = y '' (q : Set ι) :=
    (Set.image_eq_range y (q : Set ι)).symm
  have ht : Set.range (fun i : q ↦ t i) = t '' (q : Set ι) :=
    (Set.image_eq_range t (q : Set ι)).symm
  rw [hx, hy, Fintype.card_coe] at hg
  have hQ : finrank K Q = q.card := by
    have hh := finrank_span_eq_card hi
    rw [ht, Fintype.card_coe] at hh
    exact hh
  have hI : finrank K ↥(L ⊓ Q) = 1 := by
    rw [he]
    exact finrank_span_singleton hw
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq L Q
  rw [hQ, hI] at hsum
  change finrank K (Submodule.span K (x '' ((a ∪ q : Finset ι) : Set ι))) +
      finrank K (Submodule.span K (y '' ((a ∪ q : Finset ι) : Set ι))) ≤
      finrank K (Submodule.span K (t '' ((a ∪ q : Finset ι) : Set ι))) + 1
  rw [Finset.coe_union, Set.image_union, Set.image_union, Set.image_union,
    Submodule.span_union, Submodule.span_union, Submodule.span_union]
  change finrank K ↥(Submodule.span K (x '' (a : Set ι)) ⊔
      Submodule.span K (x '' (q : Set ι))) +
    finrank K ↥(Submodule.span K (y '' (a : Set ι)) ⊔
      Submodule.span K (y '' (q : Set ι))) ≤ finrank K ↥(L ⊔ Q) + 1
  change finrank K (Submodule.span K (x '' (a : Set ι))) +
    finrank K (Submodule.span K (y '' (a : Set ι))) ≤ finrank K L + 1 at ha
  omega

/-- Размерностная лемма для связного конечного семейства ненулевых простых тензоров.
Никакого ограничения характеристики и нижних границ на размеры факторов нет. -/
theorem finrank_factors_le_tensor_span_add_one
    (x : ι → X) (y : ι → Y) (s : Finset ι)
    (hconn : SpanConnected K (fun i ↦ x i ⊗ₜ[K] y i) (s : Set ι))
    (hnz : ∀ i ∈ s, x i ⊗ₜ[K] y i ≠ 0) :
    finrank K (Submodule.span K (x '' (s : Set ι))) +
      finrank K (Submodule.span K (y '' (s : Set ι))) ≤
      finrank K (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' (s : Set ι))) + 1 := by
  classical
  let t := fun i ↦ x i ⊗ₜ[K] y i
  let good := fun (a : Finset ι) ↦ a.Nonempty ∧
    finrank K (Submodule.span K (x '' (a : Set ι))) +
      finrank K (Submodule.span K (y '' (a : Set ι))) ≤
      finrank K (Submodule.span K (t '' (a : Set ι))) + 1
  let choices := s.powerset.filter good
  obtain ⟨i, hi⟩ := hconn.1
  have hxi : x i ≠ 0 := by intro h; apply hnz i hi; simp [h]
  have hyi : y i ≠ 0 := by intro h; apply hnz i hi; simp [h]
  have hsingle : ({i} : Finset ι) ∈ choices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi),
      Finset.singleton_nonempty i, ?_⟩
    rw [Finset.coe_singleton, Set.image_singleton, Set.image_singleton, Set.image_singleton]
    rw [finrank_span_singleton hxi, finrank_span_singleton hyi,
      finrank_span_singleton (hnz i hi)]
  obtain ⟨a, ha, hmax⟩ := choices.exists_max_image Finset.card ⟨{i}, hsingle⟩
  have has : a ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
  have hag : good a := (Finset.mem_filter.mp ha).2
  suffices a = s by
    subst a
    exact hag.2
  by_contra hne
  have hmeet : ¬ Disjoint (Submodule.span K (t '' (a : Set ι)))
      (Submodule.span K (t '' ((s \ a : Finset ι) : Set ι))) := by
    simpa only [Finset.coe_sdiff] using
      hconn.2 (a : Set ι) has hag.1 (by simpa using hne)
  obtain ⟨q, hqa, hqn, hqm, hqmin⟩ := exists_minimal_span_bridge t
    (Submodule.span K (t '' (a : Set ι))) (s \ a) hmeet
  have hnew : good (a ∪ q) := ⟨hag.1.mono Finset.subset_union_left,
    tensor_dimension_bound_union_of_minimal_bridge x y a q hag.2 hqm hqmin⟩
  have hnewmem : a ∪ q ∈ choices := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.union_subset has
      (fun j hj ↦ (Finset.mem_sdiff.mp (hqa hj)).1)), hnew⟩
  have hdisj : Disjoint a q := by
    apply Finset.disjoint_left.mpr
    intro j hja hjq
    exact (Finset.mem_sdiff.mp (hqa hjq)).2 hja
  have hcard := hmax (a ∪ q) hnewmem
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have := hqn.card_pos
  omega

/-- Версия для конечного множества индексов без выбора его нумерации. -/
theorem finrank_factors_le_tensor_span_add_one_of_finite
    (x : ι → X) (y : ι → Y) (s : Set ι) (hs : s.Finite)
    (hconn : SpanConnected K (fun i ↦ x i ⊗ₜ[K] y i) s)
    (hnz : ∀ i ∈ s, x i ⊗ₜ[K] y i ≠ 0) :
    finrank K (Submodule.span K (x '' s)) + finrank K (Submodule.span K (y '' s)) ≤
      finrank K (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' s)) + 1 := by
  classical
  have hc : SpanConnected K (fun i ↦ x i ⊗ₜ[K] y i) (hs.toFinset : Set ι) := by
    rw [hs.coe_toFinset]
    exact hconn
  have hn : ∀ i ∈ hs.toFinset, x i ⊗ₜ[K] y i ≠ 0 :=
    fun i hi ↦ hnz i (hs.mem_toFinset.mp hi)
  have hh := finrank_factors_le_tensor_span_add_one x y hs.toFinset hc hn
  rw [hs.coe_toFinset] at hh
  exact hh

end MMRank
