import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Finset.Powerset

/-! # Минимальное семейство, пересекающее заданное подпространство

Общая линейная лемма над произвольным полем; тензоры не требуются.
-/

namespace MMRank

open Module

variable {K ι V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Если удаление любого одного вектора уничтожает пересечение с L,
любой нулевой коэффициент представления вектора из L заставляет его занулиться. -/
theorem linearCombination_eq_zero_of_coordinate_eq_zero [Fintype ι]
    (v : ι → V) (L : Submodule K V)
    (hdelete : ∀ i, Disjoint L (Submodule.span K (v '' {i}ᶜ)))
    (c : ι → K) (hc : Fintype.linearCombination K v c ∈ L)
    (i : ι) (hi : c i = 0) : Fintype.linearCombination K v c = 0 := by
  classical
  apply (Submodule.disjoint_def.mp (hdelete i)) _ hc
  change (∑ j, c j • v j) ∈ _
  apply Submodule.sum_mem
  intro j _
  by_cases hji : j = i
  · subst j
    simp [hi]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hji, rfl⟩)

/-- Минимальное пересекающее семейство независимо; пересечение — прямая,
и каждый коэффициент её ненулевого представителя ненулевой. -/
theorem minimal_span_bridge [Fintype ι]
    (v : ι → V) (L : Submodule K V)
    (hmeet : ¬ Disjoint L (Submodule.span K (Set.range v)))
    (hdelete : ∀ i, Disjoint L (Submodule.span K (v '' {i}ᶜ))) :
    LinearIndependent K v ∧
      ∃ c : ι → K,
        (∀ i, c i ≠ 0) ∧ Fintype.linearCombination K v c ≠ 0 ∧
        L ⊓ Submodule.span K (Set.range v) = K ∙ Fintype.linearCombination K v c := by
  classical
  obtain ⟨w, hwL, hwspan, hw⟩ : ∃ w ∈ L,
      w ∈ Submodule.span K (Set.range v) ∧ w ≠ 0 := by
    simpa only [Submodule.disjoint_def, not_forall, not_imp, exists_prop] using hmeet
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hwspan
  have hcw : Fintype.linearCombination K v c = w := hc
  have hcn : ∀ i, c i ≠ 0 := by
    intro i hi
    exact hw (hcw.symm.trans
      (linearCombination_eq_zero_of_coordinate_eq_zero v L hdelete c (hcw ▸ hwL) i hi))
  have hinj : Function.Injective (Fintype.linearCombination K v) := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    have ha0 : Fintype.linearCombination K v a = 0 := ha
    ext i
    by_contra hai
    have hd : Fintype.linearCombination K v (a i • c - c i • a) = a i • w := by
      simp [map_sub, map_smul, hcw, ha0]
    have hz := linearCombination_eq_zero_of_coordinate_eq_zero v L hdelete
      (a i • c - c i • a) (hd ▸ L.smul_mem (a i) hwL) i (by simp [mul_comm])
    rw [hd, smul_eq_zero] at hz
    exact hz.elim hai hw
  have hn : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    exact hw (hcw.symm.trans (by simp [Fintype.linearCombination_apply]))
  let i := Classical.choice hn
  refine ⟨linearIndependent_iff_injective_fintypeLinearCombination.mpr hinj,
    c, hcn, hcw ▸ hw, ?_⟩
  rw [hcw]
  apply le_antisymm
  · rintro z ⟨hzL, hzspan⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hzspan
    have haz : Fintype.linearCombination K v a = z := ha
    have hd : Fintype.linearCombination K v (a - (a i / c i) • c) =
        z - (a i / c i) • w := by simp [map_sub, map_smul, haz, hcw]
    have hz := linearCombination_eq_zero_of_coordinate_eq_zero v L hdelete
      (a - (a i / c i) • c) (hd ▸ L.sub_mem hzL (L.smul_mem _ hwL)) i
      (by simp [div_mul_cancel₀ _ (hcn i)])
    rw [hd, sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨hwL, hwspan⟩

/-- Из конечного семейства с ненулевым пересечением выбирается минимальное.
Минимальность здесь по включению, а не по выбору базиса. -/
theorem exists_minimal_span_bridge (v : ι → V) (L : Submodule K V) (s : Finset ι)
    (hs : ¬ Disjoint L (Submodule.span K (v '' (s : Set ι)))) :
    ∃ q : Finset ι, q ⊆ s ∧ q.Nonempty ∧
      ¬ Disjoint L (Submodule.span K (v '' (q : Set ι))) ∧
      ∀ r ⊂ q, Disjoint L (Submodule.span K (v '' (r : Set ι))) := by
  classical
  let good := s.powerset.filter fun (q : Finset ι) ↦
    ¬ Disjoint L (Submodule.span K (v '' (q : Set ι)))
  have hg : s ∈ good := by simp [good, hs]
  obtain ⟨q, hq, hmin⟩ := good.exists_min_image Finset.card ⟨s, hg⟩
  have hqs : q ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hq).1
  have hqn := (Finset.mem_filter.mp hq).2
  refine ⟨q, hqs, ?_, hqn, ?_⟩
  · by_contra h
    have hq0 := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hq0] at hqn
  · intro r hr
    by_contra h
    have hrg : r ∈ good := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hr.subset.trans hqs), h⟩
    have := hmin r hrg
    have := Finset.card_lt_card hr
    omega

/-- Версия минимального моста для конечного подмножества исходных индексов. -/
theorem minimal_span_bridge_on_finset (v : ι → V) (L : Submodule K V) (q : Finset ι)
    (hmeet : ¬ Disjoint L (Submodule.span K (v '' (q : Set ι))))
    (hmin : ∀ r ⊂ q, Disjoint L (Submodule.span K (v '' (r : Set ι)))) :
    LinearIndependent K (fun i : q ↦ v i) ∧
      ∃ c : q → K, (∀ i, c i ≠ 0) ∧
        Fintype.linearCombination K (fun i : q ↦ v i) c ≠ 0 ∧
        L ⊓ Submodule.span K (v '' (q : Set ι)) =
          K ∙ Fintype.linearCombination K (fun i : q ↦ v i) c := by
  classical
  have hd : ∀ i : q, Disjoint L
      (Submodule.span K ((fun j : q ↦ v j) '' {i}ᶜ)) := by
    intro i
    apply (hmin (q.erase i) (Finset.erase_ssubset i.property)).mono_right
    apply Submodule.span_mono
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨j, Finset.mem_erase.mpr ⟨?_, j.property⟩, rfl⟩
    intro hji
    exact hj (Subtype.ext hji)
  have he : Set.range (fun i : q ↦ v i) = v '' (q : Set ι) :=
    (Set.image_eq_range v (q : Set ι)).symm
  simpa only [he] using
    minimal_span_bridge (fun i : q ↦ v i) L (he ▸ hmeet) hd

end MMRank
