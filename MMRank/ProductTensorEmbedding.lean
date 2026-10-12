module

public import MMRank.CoordinateComponents
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.Contraction

@[expose] public section

/-!
# Двойственное вложение произведения и координатные простые тензоры

Используется библиотечная сюръекция μ:M⊗D→MD. В математической записи
сначала применяется μ, затем форма φ; в Lean это φ.comp μ.
Вложение в M*⊗D* строится через библиотечную двойственность конечных
проективных модулей. Цена связности в этом модуле не предполагается.
-/

namespace MMRank

open scoped TensorProduct

section Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable (M D : Submodule R A)
variable [Module.Finite R M] [Module.Finite R D]
variable [Module.Projective R M] [Module.Projective R D]

/-- Двойственное отображение умножения с тензорным пространством значений. -/
noncomputable def productDualEmbedding :
    Module.Dual R (M * D) →ₗ[R] Module.Dual R M ⊗[R] Module.Dual R D :=
  (TensorProduct.dualDistribEquiv R M D).symm.toLinearMap.comp (Submodule.mulMap' M D).dualMap

theorem productDualEmbedding_injective : Function.Injective (productDualEmbedding M D) :=
  (TensorProduct.dualDistribEquiv R M D).symm.injective.comp
    (LinearMap.dualMap_injective_of_surjective (Submodule.mulMap'_surjective M D))

/-- Характеризующее равенство: сначала умножение, затем линейная форма. -/
theorem productDualEmbedding_apply (φ : Module.Dual R (M * D)) (m : M) (d : D) :
    TensorProduct.dualDistribEquiv R M D (productDualEmbedding M D φ) (m ⊗ₜ[R] d) =
      φ (Submodule.mulMap' M D (m ⊗ₜ[R] d)) := by
  simp [productDualEmbedding]

end Algebra

section Coordinates

variable {R : Type*} [CommSemiring R] {ι : Type*}
variable (M D : Submodule R (ι → R))

/-- Пара координатных оценок как простой тензор. -/
def coordinateProductTensor (i : ι) : Module.Dual R M ⊗[R] Module.Dual R D :=
  coordinateEval M i ⊗ₜ[R] coordinateEval D i

variable [Module.Finite R M] [Module.Finite R D]
variable [Module.Projective R M] [Module.Projective R D]

theorem productDualEmbedding_coordinateEval (i : ι) :
    productDualEmbedding M D (coordinateEval (M * D) i) = coordinateProductTensor M D i := by
  apply (TensorProduct.dualDistribEquiv R M D).injective
  apply TensorProduct.ext'
  intro m d
  rw [productDualEmbedding_apply]
  simp [coordinateProductTensor, coordinateEval, mul_comm]

theorem coordinateProductTensor_spanConnected_iff (s : Set ι) :
    SpanConnected R (coordinateProductTensor M D) s ↔
      SpanConnected R (coordinateEval (M * D)) s := by
  simpa only [Function.comp_def, productDualEmbedding_coordinateEval] using
    spanConnected_map_iff (productDualEmbedding M D) (productDualEmbedding_injective M D)
      (coordinateEval (M * D)) s

theorem coordinateProductTensor_ne_zero_iff (i : ι) :
    coordinateProductTensor M D i ≠ 0 ↔ ∃ x ∈ M * D, x i ≠ 0 := by
  rw [← productDualEmbedding_coordinateEval, ← map_zero (productDualEmbedding M D),
    ne_eq, (productDualEmbedding_injective M D).eq_iff, ← ne_eq, coordinateEval_ne_zero_iff]

theorem finrank_coordinateProductTensor_span (s : Set ι) :
    Module.finrank R (Submodule.span R (coordinateProductTensor M D '' s)) =
      Module.finrank R (coordinateEvalSpan (M * D) s) := by
  have he : productDualEmbedding M D ∘ coordinateEval (M * D) = coordinateProductTensor M D :=
    funext (productDualEmbedding_coordinateEval M D)
  have h := finrank_span_image_eq (productDualEmbedding M D) (productDualEmbedding_injective M D)
    (coordinateEval (M * D)) s
  rw [he] at h
  exact h

end Coordinates

section Field

variable {K : Type*} [Field K] {ι : Type*}
variable (M D : Submodule K (ι → K)) [FiniteDimensional K M] [FiniteDimensional K D]

/-- На активном каноническом блоке все координатные простые тензоры ненулевые. -/
theorem coordinateProductTensor_component_ne_zero (i : ι)
    (hi : ∃ x ∈ M * D, x i ≠ 0) {j : ι} (hj : j ∈ coordinateComponent (M * D) i) :
    coordinateProductTensor M D j ≠ 0 := by
  exact (coordinateProductTensor_ne_zero_iff M D j).mpr
    (coordinateComponent_subset_support (M * D) i hi hj)

/-- Размерность тензорной оболочки на устойчивом блоке равна размерности (MD)_s. -/
theorem finrank_coordinateProductTensor_span_of_stable
    (s : Set ι)
    (hs : ∀ x ∈ M * D, coordinateProjection K s x ∈ M * D) :
    Module.finrank K (Submodule.span K (coordinateProductTensor M D '' s)) =
      Module.finrank K (coordinateSection K (M * D) s) := by
  let := Module.Finite.of_surjective (Submodule.mulMap' M D) (Submodule.mulMap'_surjective M D)
  rw [finrank_coordinateProductTensor_span, finrank_coordinateEvalSpan_of_stable _ s hs]

omit [FiniteDimensional K M] [FiniteDimensional K D] in
/-- Каноническая компонента произведения переходит в связное семейство простых тензоров. -/
theorem coordinateProductTensor_component_connected [Finite ι] (i : ι) :
    SpanConnected K (coordinateProductTensor M D) (coordinateComponent (M * D) i) := by
  exact (coordinateProductTensor_spanConnected_iff M D _).mpr
    (coordinateComponent_evalSpan_connected (M * D) i)

end Field

section Saturated

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

/-- Данные активного блока, используемые в тензорной размерностной лемме.
Само неравенство цены связности здесь не предполагается. -/
theorem saturated_component_tensor_data (M N : Submodule K (ι → K)) (i : ι)
    (hi : ∃ x ∈ M * conductor N M, x i ≠ 0) :
    let D := conductor N M
    let E := M * D
    let C := coordinateComponent E i
    SpanConnected K (coordinateProductTensor M D) C ∧
      (∀ j ∈ C, coordinateProductTensor M D j ≠ 0) ∧
      Module.finrank K (Submodule.span K (coordinateProductTensor M D '' C)) =
        Module.finrank K (coordinateSection K E C) ∧
      Module.finrank K (coordinateEvalSpan M C) =
        Module.finrank K (coordinateRestriction M C).range ∧
      Module.finrank K (coordinateEvalSpan D C) =
        Module.finrank K (coordinateSection K D C) := by
  dsimp only
  have he := coordinateComponent_stable (M * conductor N M) i
  have hd := (saturated_coordinateProjection_stable_iff M N _).mpr he
  exact ⟨coordinateProductTensor_component_connected M _ i,
    fun _ hj ↦ coordinateProductTensor_component_ne_zero M _ i hi hj,
    finrank_coordinateProductTensor_span_of_stable M _ _ he,
    finrank_coordinateEvalSpan M _, finrank_coordinateEvalSpan_of_stable _ _ hd⟩

end Saturated

end MMRank
