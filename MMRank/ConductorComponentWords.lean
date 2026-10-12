import MMRank.ActiveCoordinateComponents
import MMRank.PointWords

namespace MMRank
open Module
variable {K I : Type*} [Field K] [Finite I]

/-- Умножение на слово и ограничение на его точный носитель имеют одинаковый
ранг, даже если умножение не инъективно на всём M. -/
theorem finrank_mul_word_eq_restriction (M : Submodule K (I → K)) (w : I → K) :
    finrank K (M.map (LinearMap.mulRight K w)) =
      finrank K (coordinateRestriction M {i | w i ≠ 0}).range := by
  let f := (LinearMap.mulRight K w).comp M.subtype
  let g := coordinateRestriction M {i | w i ≠ 0}
  have hk : f.ker = g.ker := by
    ext a
    constructor
    · intro ha
      ext i
      exact (mul_eq_zero.mp (congrFun ha i.val)).resolve_right i.property
    · intro ha
      ext i
      by_cases hi : w i = 0
      · change a.val i * w i = 0; rw [hi, mul_zero]
      · change a.val i * w i = 0
        rw [show a.val i = 0 from congrFun ha ⟨i, hi⟩, zero_mul]
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hr : f.range = M.map (LinearMap.mulRight K w) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hr, hk] at hf
  exact Nat.add_right_cancel (hf.trans hg.symm)

/-- Один элемент кондуктора реализует точный носитель активной канонической
компоненты насыщенного пространства. Произвольная точка не объявляется блоком. -/
theorem exists_conductor_word_support_component [Infinite K]
    (M N : Submodule K (I → K)) (h1 : (1 : I → K) ∈ M) (i : I)
    (hi : ∃ w ∈ M * conductor N M, w i ≠ 0) :
    ∃ d ∈ coordinateSection K (conductor N M) (coordinateComponent (M * conductor N M) i),
      d ≠ 0 ∧ {j | d j ≠ 0} = coordinateComponent (M * conductor N M) i := by
  have hd := (product_coord_nonzero_iff M (conductor N M) h1 i).mp hi
  let c : activeCoordinateComponents (conductor N M) :=
    ⟨coordinateComponent (conductor N M) i, coordinateComponent_mem_active _ i hd⟩
  obtain ⟨d, hd, h0, hs⟩ := exists_mem_support_eq_activeComponent (conductor N M) c
  dsimp only [c] at hd hs
  rw [saturated_coordinateComponent_eq] at hd hs
  exact ⟨d, hd, h0, hs⟩

omit [Finite I] in
/-- Одномерное сечение кондуктора, порождающее двумерное насыщенное сечение,
не содержит точечных слов даже в большем поддержанном пространстве N. -/
theorem hasNoPointWords_of_one_dimensional_conductor_section
    (M N : Submodule K (I → K)) (h1 : (1 : I → K) ∈ M) (G : Set I)
    (hd : finrank K (coordinateSection K (conductor N M) G) = 1)
    (he : 2 ≤ finrank K (M * coordinateSection K (conductor N M) G)) :
    HasNoPointWords M (coordinateSection K N G) := by
  intro w hw hp
  have hwD : w ∈ coordinateSection K (conductor N M) G :=
    mem_coordinateSection.mpr ⟨hp.mem_conductor (mem_coordinateSection.mp hw).1,
      (mem_coordinateSection.mp hw).2⟩
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hwD hp.1
  have hmul : M * coordinateSection K (conductor N M) G = Submodule.span K {w} := by
    rw [hspan]
    apply le_antisymm
    · apply Submodule.mul_le.mpr
      intro a ha b hb
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
      rw [mul_smul_comm]
      obtain ⟨t, ht⟩ := hp.2 a ha
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr ⟨t, ht.symm⟩)
    · exact le_mul_of_one_mem M _ h1
  rw [hmul, finrank_span_singleton hp.1] at he
  omega

end MMRank
