module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Связность линейного семейства и перенос при вложении

Отсутствие прямого разделения формулируется отдельно от ненулевости векторов.
Свойства доказаны над полукольцом для произвольного множества индексов.
Равенство finrank использует библиотечную конвенцию finrank=0 при бесконечном ранге.
-/

namespace MMRank

section Semiring

variable (R : Type*) [Semiring R] {ι V W : Type*}
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Непустое семейство не разделяется на две части с независимо суммирующимися
оболочками. Ненулевость отдельных векторов — отдельное условие. -/
def SpanConnected (v : ι → V) (s : Set ι) : Prop :=
  s.Nonempty ∧ ∀ t ⊆ s, t.Nonempty → t ≠ s →
    ¬ Disjoint (Submodule.span R (v '' t)) (Submodule.span R (v '' (s \ t)))

variable {R}

/-- Инъективное линейное отображение сохраняет и отражает разделение оболочек. -/
theorem disjoint_span_image_iff (f : V →ₗ[R] W) (hf : Function.Injective f)
    (v : ι → V) (s t : Set ι) :
    Disjoint (Submodule.span R ((f ∘ v) '' s)) (Submodule.span R ((f ∘ v) '' t)) ↔
      Disjoint (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) := by
  simp only [Function.comp_def]
  rw [← Set.image_image (⇑f) v s, ← Set.image_image (⇑f) v t,
    ← Submodule.map_span, ← Submodule.map_span,
    disjoint_iff, ← Submodule.map_inf _ hf, ← Submodule.map_bot f,
    (Submodule.map_injective_of_injective hf).eq_iff, disjoint_iff]

theorem spanConnected_map_iff (f : V →ₗ[R] W) (hf : Function.Injective f)
    (v : ι → V) (s : Set ι) : SpanConnected R (f ∘ v) s ↔ SpanConnected R v s := by
  simp only [SpanConnected, disjoint_span_image_iff f hf]

end Semiring

section Dimension

variable {K : Type*} [Semiring K] {ι V W : Type*}
variable [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- Размерность любой оболочки сохраняется при инъективном линейном отображении. -/
theorem finrank_span_image_eq (f : V →ₗ[K] W) (hf : Function.Injective f)
    (v : ι → V) (s : Set ι) :
    Module.finrank K (Submodule.span K ((f ∘ v) '' s)) =
      Module.finrank K (Submodule.span K (v '' s)) := by
  have h : (Submodule.span K (v '' s)).map f = Submodule.span K ((f ∘ v) '' s) := by
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [← h]
  exact (Submodule.equivMapOfInjective f hf (Submodule.span K (v '' s))).finrank_eq.symm

end Dimension

end MMRank
