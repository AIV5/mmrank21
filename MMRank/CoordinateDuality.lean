module

public import MMRank.CoordinateDecomposition
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# Координатные оценки и двойственный критерий разложения

Проекторы действуют справа в математической записи; Lean использует обычное
применение линейного отображения. Сечение и образ ограничения различаются.
-/

namespace MMRank

section Semiring

variable {R : Type*} [CommSemiring R] {ι : Type*}

/-- Координатная оценка на подмодуле слов. -/
def coordinateEval (N : Submodule R (ι → R)) (i : ι) : Module.Dual R N :=
  (LinearMap.proj i).comp N.subtype

@[simp] theorem coordinateEval_apply (N : Submodule R (ι → R)) (i : ι) (x : N) :
    coordinateEval N i x = x.val i := rfl

/-- Ненулевая оценка означает наличие этой координаты в носителе пространства. -/
theorem coordinateEval_ne_zero_iff (N : Submodule R (ι → R)) (i : ι) :
    coordinateEval N i ≠ 0 ↔ ∃ x ∈ N, x i ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    ext x
    exact hn x.val x.property
  · rintro ⟨x, hx, hi⟩ h
    exact hi (congrArg (fun φ : Module.Dual R N ↦ φ ⟨x, hx⟩) h)

/-- Оболочка координатных оценок на заданном множестве индексов. -/
def coordinateEvalSpan (N : Submodule R (ι → R)) (s : Set ι) :
    Submodule R (Module.Dual R N) := Submodule.span R (coordinateEval N '' s)

/-- Ограничение слова N на s; в отличие от сечения не требует зануления вне s. -/
def coordinateRestriction (N : Submodule R (ι → R)) (s : Set ι) : N →ₗ[R] (s → R) :=
  LinearMap.pi fun i ↦ coordinateEval N i.val

@[simp] theorem coordinateRestriction_apply (N : Submodule R (ι → R)) (s : Set ι)
    (x : N) (i : s) : coordinateRestriction N s x i = x.val i := rfl

theorem mem_coordinateEvalSpan_coannihilator (N : Submodule R (ι → R))
    (s : Set ι) (x : N) :
    x ∈ (coordinateEvalSpan N s).dualCoannihilator ↔ ∀ i ∈ s, x.val i = 0 := by
  change x ∈ ((Submodule.span R (coordinateEval N '' s)).dualCoannihilator : Set N) ↔ _
  rw [Submodule.coe_dualCoannihilator_span]
  simp

/-- Аннулятор оценок на s — слова, зануляющиеся на s, то есть сечение по дополнению. -/
theorem coordinateEvalSpan_coannihilator_map (N : Submodule R (ι → R)) (s : Set ι) :
    (coordinateEvalSpan N s).dualCoannihilator.map N.subtype = coordinateSection R N sᶜ := by
  ext x
  simp only [Submodule.mem_map, mem_coordinateEvalSpan_coannihilator, mem_coordinateSection,
    Set.mem_compl_iff, not_not, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hz⟩
    exact ⟨⟨x, hx⟩, hz, rfl⟩

theorem coordinateRestriction_ker (N : Submodule R (ι → R)) (s : Set ι) :
    (coordinateRestriction N s).ker = (coordinateEvalSpan N s).dualCoannihilator := by
  ext x
  rw [mem_coordinateEvalSpan_coannihilator]
  simp [LinearMap.mem_ker, funext_iff]

theorem coordinateEvalSpan_union (N : Submodule R (ι → R)) (s t : Set ι) :
    coordinateEvalSpan N (s ∪ t) = coordinateEvalSpan N s ⊔ coordinateEvalSpan N t := by
  simp only [coordinateEvalSpan, Set.image_union, Submodule.span_union]

end Semiring

section Field

variable {K : Type*} [Field K] {ι : Type*}
variable (N : Submodule K (ι → K)) [FiniteDimensional K N]

/-- Координатные оценки порождают N*, даже при бесконечном множестве координат. -/
theorem coordinateEvalSpan_univ : coordinateEvalSpan N Set.univ = ⊤ := by
  have h : (coordinateEvalSpan N Set.univ).dualCoannihilator = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    apply Subtype.ext
    funext i
    exact (mem_coordinateEvalSpan_coannihilator N Set.univ x).mp hx i trivial
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := coordinateEvalSpan N Set.univ),
    h, Submodule.dualAnnihilator_bot]

/-- Ранг оболочки оценок равен размерности образа ограничения, не внутреннего сечения. -/
theorem finrank_coordinateEvalSpan (s : Set ι) :
    Module.finrank K (coordinateEvalSpan N s) =
      Module.finrank K (coordinateRestriction N s).range := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (coordinateEvalSpan N s)
  have g := LinearMap.finrank_range_add_finrank_ker (coordinateRestriction N s)
  rw [coordinateRestriction_ker] at g
  exact Nat.add_right_cancel (h.trans g.symm)

/-- Разделимость оболочек оценок эквивалентна координатному разложению N. -/
theorem coordinateEvalSpan_disjoint_iff_section_sup (s : Set ι) :
    Disjoint (coordinateEvalSpan N s) (coordinateEvalSpan N sᶜ) ↔
      coordinateSection K N s ⊔ coordinateSection K N sᶜ = N := by
  rw [disjoint_iff,
    ← Subspace.dualCoannihilator_dualAnnihilator_eq
      (W := coordinateEvalSpan N s ⊓ coordinateEvalSpan N sᶜ),
    Submodule.dualAnnihilator_eq_bot_iff, Subspace.dualCoannihilator_inf,
    ← (Submodule.map_injective_of_injective N.injective_subtype).eq_iff,
    Submodule.map_sup, coordinateEvalSpan_coannihilator_map,
    coordinateEvalSpan_coannihilator_map, compl_compl, Submodule.map_top,
    Submodule.range_subtype, sup_comm]

/-- Двойственный критерий устойчивости координатного проектора. -/
theorem coordinateProjection_stable_iff_evalSpan_disjoint (s : Set ι) :
    (∀ x ∈ N, coordinateProjection K s x ∈ N) ↔
      Disjoint (coordinateEvalSpan N s) (coordinateEvalSpan N sᶜ) := by
  rw [coordinateEvalSpan_disjoint_iff_section_sup]
  constructor
  · intro hs
    exact coordinateSection_sup_compl N s hs (coordinateProjection_compl_stable N s hs)
  · intro h x hx
    rw [← h] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨ha, haz⟩ := mem_coordinateSection.mp ha
    obtain ⟨hb, hbz⟩ := mem_coordinateSection.mp hb
    have hbp : coordinateProjection K s b = 0 := by
      ext i
      by_cases hi : i ∈ s
      · simp [hi, hbz i (by simpa using hi)]
      · simp [hi]
    rw [map_add, coordinateProjection_eq_self haz, hbp, add_zero]
    exact ha

/-- На устойчивом блоке размерности оболочки оценок и внутреннего сечения совпадают. -/
theorem finrank_coordinateEvalSpan_of_stable (s : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection K s x ∈ N) :
    Module.finrank K (coordinateEvalSpan N s) = Module.finrank K (coordinateSection K N s) := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (coordinateEvalSpan N s)
  have he := coordinateEvalSpan_coannihilator_map N s
  have hd : Module.finrank K (coordinateEvalSpan N s).dualCoannihilator =
      Module.finrank K (coordinateSection K N sᶜ) := by
    rw [← he, Submodule.finrank_map_subtype_eq]
  rw [hd] at h
  exact Nat.add_right_cancel (h.trans (finrank_coordinateSection_add_compl N s hs).symm)

end Field

end MMRank
