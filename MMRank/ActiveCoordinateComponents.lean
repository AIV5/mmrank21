module

public import MMRank.ConnectivityCost
public import MMRank.ConductorSupportInjection

@[expose] public section

/-! # Активные координатные компоненты без нулевых блоков -/

namespace MMRank
open Module
variable {K I : Type*} [Field K] [Finite I]

/-- Канонические блоки с ненулевым сечением. Нулевые одноточечные блоки исключены. -/
def activeCoordinateComponents (N : Submodule K (I → K)) : Set (Set I) :=
  {s | s ∈ Set.range (coordinateComponent N) ∧ coordinateSection K N s ≠ ⊥}

/-- Любая ненулевая координата пространства принадлежит активной компоненте. -/
theorem coordinateComponent_mem_active (N : Submodule K (I → K)) (i : I)
    (hi : ∃ w ∈ N, w i ≠ 0) : coordinateComponent N i ∈ activeCoordinateComponents N := by
  refine ⟨⟨i, rfl⟩, ?_⟩
  obtain ⟨w, hw, hwi⟩ := hi
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨coordinateProjection K (coordinateComponent N i) w,
    mem_coordinateSection.mpr ⟨coordinateComponent_stable N i w hw,
      fun j hj ↦ by simp [hj]⟩, ?_⟩
  exact fun hz ↦ hwi (by simpa [mem_coordinateComponent_self] using congrFun hz i)

/-- Активные блоки покрывают ровно носитель N, а не все координаты. -/
theorem iUnion_activeCoordinateComponents (N : Submodule K (I → K)) :
    (⋃ c : activeCoordinateComponents N, c.val) = {i | ∃ w ∈ N, w i ≠ 0} := by
  ext i
  constructor
  · intro hi
    obtain ⟨c, hic⟩ := Set.mem_iUnion.mp hi
    obtain ⟨j, hj⟩ := c.property.1
    obtain ⟨w, hw, hw0⟩ := (coordinateSection K N c.val).ne_bot_iff.mp c.property.2
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by simpa [funext_iff] using hw0
    have hkc : k ∈ c.val := by
      by_contra hn
      exact hk ((mem_coordinateSection.mp hw).2 k hn)
    have he := coordinateComponent_eq_of_mem N (hj ▸ hkc)
    exact coordinateComponent_subset_support N k ⟨w, (mem_coordinateSection.mp hw).1, hk⟩
      (he ▸ hj ▸ hic)
  · intro hi
    exact Set.mem_iUnion.mpr ⟨⟨coordinateComponent N i, coordinateComponent_mem_active N i hi⟩,
      mem_coordinateComponent_self N i⟩

omit [Finite I] in
theorem activeCoordinateComponents_pairwise_disjoint (N : Submodule K (I → K)) :
    Pairwise (fun a b : activeCoordinateComponents N ↦ Disjoint a.val b.val) := by
  intro a b hab
  exact coordinateBlocks_pairwise_disjoint N
    (i := ⟨a.val, a.property.1⟩) (j := ⟨b.val, b.property.1⟩)
    (fun he ↦ hab (Subtype.ext
      (congrArg (fun x : Set.range (coordinateComponent N) ↦ x.val) he)))

/-- Удаление нулевых блоков сохраняет внутреннюю прямую сумму. -/
theorem activeCoordinateComponents_direct (N : Submodule K (I → K)) :
    iSupIndep (fun c : activeCoordinateComponents N ↦ coordinateSection K N c.val) ∧
      (⨆ c : activeCoordinateComponents N, coordinateSection K N c.val) = N := by
  refine ⟨coordinateSections_iSupIndep N _ (activeCoordinateComponents_pairwise_disjoint N), ?_⟩
  apply le_antisymm (iSup_le fun _ ↦ inf_le_left)
  conv_lhs => rw [← (coordinateComponents_direct N).2]
  apply iSup_le
  intro c
  by_cases hz : coordinateSection K N c.val = ⊥
  · rw [hz]; exact bot_le
  · exact le_iSup (fun c : activeCoordinateComponents N ↦ coordinateSection K N c.val)
      ⟨c.val, c.property, hz⟩

/-- Над бесконечным полем активный канонический блок является точным носителем
одного слова своего сечения. Устойчивость получена из определения компоненты. -/
theorem exists_mem_support_eq_activeComponent [Infinite K]
    (N : Submodule K (I → K)) (c : activeCoordinateComponents N) :
    ∃ w ∈ coordinateSection K N c.val, w ≠ 0 ∧ {i | w i ≠ 0} = c.val := by
  obtain ⟨i, hi⟩ := c.property.1
  obtain ⟨w, hw, hws⟩ := exists_mem_support_eq (coordinateSection K N c.val)
  have hsupp : {k | w k ≠ 0} = c.val := by
    ext k
    constructor
    · intro hk
      by_contra hn
      exact hk ((mem_coordinateSection.mp hw).2 k hn)
    · intro hk
      have hkn : ∃ v ∈ N, v k ≠ 0 := by
        change k ∈ {j | ∃ v ∈ N, v j ≠ 0}
        rw [← iUnion_activeCoordinateComponents N]
        exact Set.mem_iUnion.mpr ⟨c, hk⟩
      obtain ⟨v, hv, hvk⟩ := hkn
      apply (hws k).mpr
      refine ⟨coordinateProjection K c.val v,
        mem_coordinateSection.mpr ⟨hi ▸ coordinateComponent_stable N i v hv,
          fun j hj ↦ by simp [hj]⟩, ?_⟩
      simpa [hk] using hvk
  refine ⟨w, hw, ?_, hsupp⟩
  intro hz
  have hic := hi ▸ mem_coordinateComponent_self N i
  rw [← hsupp] at hic
  exact hic (congrFun hz i)

end MMRank
