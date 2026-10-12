module

public import MMRank.CoordinateDuality
public import MMRank.SpanConnected
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-!
# Канонические координатные компоненты

Компоненты определяются всеми устойчивыми координатными разрезами, без выбора
базиса или порядка индексов. При конечном множестве координат они устойчивы,
дают прямые суммы исходного и двойственного пространств и связны по оценкам.
Вне носителя оставлены одноточечные нулевые блоки; блок активного индекса
целиком лежит в носителе. Цена связности здесь ещё не доказывается.
-/

namespace MMRank

section Semiring

variable {R : Type*} [CommSemiring R] {ι : Type*}

theorem coordinateProjection_inter (s t : Set ι) (x : ι → R) :
    coordinateProjection R (s ∩ t) x =
      coordinateProjection R s (coordinateProjection R t x) := by
  classical
  ext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht]

theorem coordinateProjection_inter_stable (N : Submodule R (ι → R)) (s t : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection R s x ∈ N)
    (ht : ∀ x ∈ N, coordinateProjection R t x ∈ N) :
    ∀ x ∈ N, coordinateProjection R (s ∩ t) x ∈ N := by
  intro x hx
  rw [coordinateProjection_inter]
  exact hs _ (ht x hx)

theorem coordinateProjection_sInter_stable (N : Submodule R (ι → R))
    (S : Set (Set ι)) (hS : S.Finite)
    (hs : ∀ s ∈ S, ∀ x ∈ N, coordinateProjection R s x ∈ N) :
    ∀ x ∈ N, coordinateProjection R (⋂₀ S) x ∈ N := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro x hx
      rw [Set.sInter_empty, coordinateProjection_eq_self (by simp)]
      exact hx
  | @insert s S hnot hfin ih =>
      rw [Set.sInter_insert]
      exact coordinateProjection_inter_stable N s (⋂₀ S)
        (hs s (by simp)) (ih (fun t ht ↦ hs t (by simp [ht])))

/-- Наименьший устойчивый координатный блок, содержащий i.
Устойчивость самого пересечения ниже доказана при конечном ι. -/
def coordinateComponent (N : Submodule R (ι → R)) (i : ι) : Set ι :=
  ⋂₀ {s | (∀ x ∈ N, coordinateProjection R s x ∈ N) ∧ i ∈ s}

theorem mem_coordinateComponent_self (N : Submodule R (ι → R)) (i : ι) :
    i ∈ coordinateComponent N i := by
  intro s hs
  exact hs.2

theorem coordinateComponent_subset (N : Submodule R (ι → R)) (i : ι) (s : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection R s x ∈ N) (hi : i ∈ s) :
    coordinateComponent N i ⊆ s := by
  intro j hj
  exact hj s ⟨hs, hi⟩

theorem coordinateComponent_stable [Finite ι] (N : Submodule R (ι → R)) (i : ι) :
    ∀ x ∈ N, coordinateProjection R (coordinateComponent N i) x ∈ N := by
  exact coordinateProjection_sInter_stable N _ (Set.toFinite _) (fun _ h ↦ h.1)

/-- Насыщенная пара имеет одни и те же канонические координатные блоки. -/
theorem saturated_coordinateComponent_eq (M N : Submodule R (ι → R)) (i : ι) :
    coordinateComponent (conductor N M) i = coordinateComponent (M * conductor N M) i := by
  unfold coordinateComponent
  congr 1
  ext s
  exact and_congr (saturated_coordinateProjection_stable_iff M N s) Iff.rfl

/-- Сечения по попарно непересекающимся множествам образуют независимое семейство. -/
theorem coordinateSections_iSupIndep (N : Submodule R (ι → R)) {β : Type*}
    (b : β → Set ι) (hd : Pairwise (fun a c ↦ Disjoint (b a) (b c))) :
    iSupIndep (fun a ↦ coordinateSection R N (b a)) := by
  intro a
  apply (coordinateSection_disjoint N (b a)).mono_right
  refine iSup_le fun c ↦ iSup_le fun hca ↦ ?_
  intro x hx
  obtain ⟨hx, hz⟩ := mem_coordinateSection.mp hx
  apply mem_coordinateSection.mpr
  refine ⟨hx, ?_⟩
  intro i hi
  have hia : i ∈ b a := by simpa using hi
  exact hz i (fun hic ↦ Set.disjoint_left.mp (hd hca) hic hia)

/-- Конечное разбиение координат даёт сумму проекторов, равную единице. -/
theorem sum_coordinateProjection_eq {β : Type*} [Fintype β] (b : β → Set ι)
    (hd : Pairwise (fun a c ↦ Disjoint (b a) (b c)))
    (hc : ∀ i, ∃ a, i ∈ b a) (x : ι → R) :
    ∑ a, coordinateProjection R (b a) x = x := by
  classical
  ext i
  obtain ⟨a, ha⟩ := hc i
  rw [Finset.sum_apply, Finset.sum_eq_single a]
  · simp [ha]
  · intro c _ hca
    have hi : i ∉ b c := fun hic ↦ Set.disjoint_left.mp (hd hca) hic ha
    simp [hi]
  · simp

/-- Устойчивое конечное разбиение даёт всё исходное пространство как сумму сечений. -/
theorem coordinateSections_iSup_eq {β : Type*} [Finite β]
    (N : Submodule R (ι → R)) (b : β → Set ι)
    (hd : Pairwise (fun a c ↦ Disjoint (b a) (b c)))
    (hc : ∀ i, ∃ a, i ∈ b a)
    (hs : ∀ a, ∀ x ∈ N, coordinateProjection R (b a) x ∈ N) :
    (⨆ a, coordinateSection R N (b a)) = N := by
  classical
  let := Fintype.ofFinite β
  apply le_antisymm (iSup_le fun _ ↦ inf_le_left)
  intro x hx
  rw [← sum_coordinateProjection_eq b hd hc x]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.mem_iSup_of_mem a
  exact mem_coordinateSection.mpr ⟨hs a x hx, by intro i hi; simp [hi]⟩

end Semiring

section Ring

variable {R : Type*} [CommRing R] {ι : Type*}

/-- Два индекса лежат в одном блоке тогда и только тогда, когда никакой
устойчивый координатный проектор не разделяет их. -/
theorem mem_coordinateComponent_iff (N : Submodule R (ι → R)) (i j : ι) :
    j ∈ coordinateComponent N i ↔
      ∀ s : Set ι, (∀ x ∈ N, coordinateProjection R s x ∈ N) → (i ∈ s ↔ j ∈ s) := by
  constructor
  · intro h s hs
    constructor
    · intro hi
      exact coordinateComponent_subset N i s hs hi h
    · intro hj
      by_contra hi
      have hc := coordinateComponent_subset N i sᶜ
        (coordinateProjection_compl_stable N s hs) hi h
      exact hc hj
  · intro h s hs
    exact (h s hs.1).mp hs.2

theorem coordinateComponent_eq_of_mem (N : Submodule R (ι → R)) {i j : ι}
    (h : j ∈ coordinateComponent N i) : coordinateComponent N i = coordinateComponent N j := by
  rw [mem_coordinateComponent_iff] at h
  ext k
  simp only [mem_coordinateComponent_iff]
  exact forall_congr' fun s ↦ forall_congr' fun hs ↦ iff_congr (h s hs) Iff.rfl

/-- Канонические блоки равны или не пересекаются. -/
theorem coordinateComponent_eq_or_disjoint (N : Submodule R (ι → R)) (i j : ι) :
    coordinateComponent N i = coordinateComponent N j ∨
      Disjoint (coordinateComponent N i) (coordinateComponent N j) := by
  by_cases h : Disjoint (coordinateComponent N i) (coordinateComponent N j)
  · exact Or.inr h
  · left
    obtain ⟨k, hi, hj⟩ := Set.not_disjoint_iff.mp h
    exact (coordinateComponent_eq_of_mem N hi).trans (coordinateComponent_eq_of_mem N hj).symm

/-- Различные канонические блоки индексируются без повторений через range. -/
theorem coordinateBlocks_pairwise_disjoint (N : Submodule R (ι → R)) :
    Pairwise (fun a b : Set.range (coordinateComponent N) ↦ Disjoint a.val b.val) := by
  rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
  exact (coordinateComponent_eq_or_disjoint N i j).resolve_left
    (fun h ↦ hne (Subtype.ext h))

/-- Канонические блоки дают внутреннюю прямую сумму N; нулевые блоки разрешены. -/
theorem coordinateComponents_direct [Finite ι] (N : Submodule R (ι → R)) :
    iSupIndep (fun c : Set.range (coordinateComponent N) ↦ coordinateSection R N c.val) ∧
      (⨆ c : Set.range (coordinateComponent N), coordinateSection R N c.val) = N := by
  refine ⟨coordinateSections_iSupIndep N _ (coordinateBlocks_pairwise_disjoint N), ?_⟩
  apply coordinateSections_iSup_eq N _ (coordinateBlocks_pairwise_disjoint N)
  · intro i
    exact ⟨⟨coordinateComponent N i, ⟨i, rfl⟩⟩, mem_coordinateComponent_self N i⟩
  · rintro ⟨_, i, rfl⟩
    exact coordinateComponent_stable N i

/-- В устойчивом блоке нельзя выделить непустой собственный устойчивый блок. -/
theorem coordinateComponent_minimal (N : Submodule R (ι → R)) (i : ι) (s : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection R s x ∈ N)
    (hle : s ⊆ coordinateComponent N i) (hne : s.Nonempty) : s = coordinateComponent N i := by
  obtain ⟨j, hj⟩ := hne
  apply Set.Subset.antisymm hle
  rw [coordinateComponent_eq_of_mem N (hle hj)]
  exact coordinateComponent_subset N j s hs hj

/-- Нулевая координата образует отдельный блок, который не даёт ненулевого сечения. -/
theorem coordinateComponent_eq_singleton_of_eval_zero (N : Submodule R (ι → R)) (i : ι)
    (hz : ∀ x ∈ N, x i = 0) : coordinateComponent N i = {i} := by
  classical
  apply Set.Subset.antisymm
  · apply coordinateComponent_subset N i {i} ?_ (by simp)
    intro x hx
    have h : coordinateProjection R {i} x = 0 := by
      ext j
      simp only [coordinateProjection_apply, Set.indicator_singleton,
        hz x hx, Pi.single_zero, Pi.zero_apply]
    rw [h]
    exact N.zero_mem
  · exact Set.singleton_subset_iff.mpr (mem_coordinateComponent_self N i)

/-- Блок активного индекса целиком лежит в носителе N. -/
theorem coordinateComponent_subset_support (N : Submodule R (ι → R)) (i : ι)
    (hi : ∃ x ∈ N, x i ≠ 0) {j : ι} (hj : j ∈ coordinateComponent N i) :
    ∃ x ∈ N, x j ≠ 0 := by
  by_contra hz
  push Not at hz
  have he := (coordinateComponent_eq_of_mem N hj).trans
    (coordinateComponent_eq_singleton_of_eval_zero N j hz)
  have hij : i = j := by
    have h := mem_coordinateComponent_self N i
    rwa [he, Set.mem_singleton_iff] at h
  subst j
  obtain ⟨x, hx, hxi⟩ := hi
  exact hxi (hz x hx)

end Ring

section Field

variable {K : Type*} [Field K] {ι : Type*}

/-- Устойчивые попарно непересекающиеся блоки дают независимые оболочки оценок. -/
theorem coordinateEvalSpans_iSupIndep (N : Submodule K (ι → K)) [FiniteDimensional K N]
    {β : Type*} (b : β → Set ι) (hd : Pairwise (fun a c ↦ Disjoint (b a) (b c)))
    (hs : ∀ a, ∀ x ∈ N, coordinateProjection K (b a) x ∈ N) :
    iSupIndep (fun a ↦ coordinateEvalSpan N (b a)) := by
  intro a
  apply ((coordinateProjection_stable_iff_evalSpan_disjoint N (b a)).mp (hs a)).mono_right
  refine iSup_le fun c ↦ iSup_le fun hca ↦ ?_
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  exact fun hia ↦ Set.disjoint_left.mp (hd hca) hi hia

/-- Оболочки оценок на покрывающем семействе блоков порождают всё N*. -/
theorem coordinateEvalSpans_iSup_eq_top (N : Submodule K (ι → K)) [FiniteDimensional K N]
    {β : Type*} (b : β → Set ι) (hc : ∀ i, ∃ a, i ∈ b a) :
    (⨆ a, coordinateEvalSpan N (b a)) = ⊤ := by
  apply top_unique
  rw [← coordinateEvalSpan_univ N]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, _, rfl⟩
  obtain ⟨a, ha⟩ := hc i
  exact Submodule.mem_iSup_of_mem a (Submodule.subset_span ⟨i, ha, rfl⟩)

/-- Канонические компоненты дают прямую сумму оболочек оценок в N*. -/
theorem coordinateComponents_dual_direct [Finite ι] (N : Submodule K (ι → K)) :
    iSupIndep (fun c : Set.range (coordinateComponent N) ↦ coordinateEvalSpan N c.val) ∧
      (⨆ c : Set.range (coordinateComponent N), coordinateEvalSpan N c.val) = ⊤ := by
  constructor
  · apply coordinateEvalSpans_iSupIndep N _ (coordinateBlocks_pairwise_disjoint N)
    rintro ⟨_, i, rfl⟩
    exact coordinateComponent_stable N i
  · apply coordinateEvalSpans_iSup_eq_top
    intro i
    exact ⟨⟨coordinateComponent N i, ⟨i, rfl⟩⟩, mem_coordinateComponent_self N i⟩

/-- Разделение оценок внутри устойчивого блока даёт устойчивый подблок. -/
theorem coordinateProjection_stable_of_evalSpan_split
    (N : Submodule K (ι → K)) [FiniteDimensional K N] (c s : Set ι)
    (hle : s ⊆ c) (hc : ∀ x ∈ N, coordinateProjection K c x ∈ N)
    (hs : Disjoint (coordinateEvalSpan N s) (coordinateEvalSpan N (c \ s))) :
    ∀ x ∈ N, coordinateProjection K s x ∈ N := by
  have hcu : s ∪ (c \ s) = c := by
    rw [Set.union_sdiff_self, Set.union_eq_self_of_subset_left hle]
  have hsc : (c \ s) ∪ cᶜ = sᶜ := by
    simpa only [Set.compl_eq_univ_sdiff, Set.union_comm] using
      Set.sdiff_union_sdiff_cancel (Set.subset_univ c) hle
  have hd := (coordinateProjection_stable_iff_evalSpan_disjoint N c).mp hc
  have hsp : coordinateEvalSpan N s ⊔ coordinateEvalSpan N (c \ s) =
      coordinateEvalSpan N c := by rw [← coordinateEvalSpan_union, hcu]
  rw [← hsp] at hd
  have h := hs.disjoint_sup_right_of_disjoint_sup_left hd
  rw [← coordinateEvalSpan_union, hsc] at h
  exact (coordinateProjection_stable_iff_evalSpan_disjoint N s).mpr h

/-- Никакое непустое собственное подсемейство оценок компоненты не отделяется
прямой суммой от остальных оценок той же компоненты. -/
theorem coordinateComponent_evalSpan_connected [Finite ι]
    (N : Submodule K (ι → K)) (i : ι) :
    SpanConnected K (coordinateEval N) (coordinateComponent N i) := by
  refine ⟨⟨i, mem_coordinateComponent_self N i⟩, ?_⟩
  intro s hle hne hproper hd
  have hs := coordinateProjection_stable_of_evalSpan_split N _ s hle
    (coordinateComponent_stable N i) hd
  exact hproper (coordinateComponent_minimal N i s hs hle hne)

end Field

end MMRank
