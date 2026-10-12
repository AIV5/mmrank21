module

public import MMRank.PhysicalContractions
public import MMRank.SeparableMapDimension
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! # Физические верхние оценки насыщенной оболочки

Из двух тождеств Qᵢ выводятся ps+(q−1)e≤ℓ и qe≤|supp D|.
Размеры и характеристика произвольны; нормировка 1∈A_F не требуется.
-/

namespace MMRank

open Matrix Module
open scoped BigOperators

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Следовое спаривание физических выходов и тестовых матриц. -/
def matrixTracePairing : Matrix P S K →ₗ[K] Matrix S P K →ₗ[K] K :=
  (mulLinearMap K).flip.compr₂ (traceLinearMap S K K)

@[simp] theorem matrixTracePairing_apply (C : Matrix P S K) (N : Matrix S P K) :
    matrixTracePairing C N = trace (N * C) := rfl

theorem matrixTracePairing_injective :
    Function.Injective (matrixTracePairing (K := K) (P := P) (S := S)) := by
  intro C C' h
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro N
  exact DFunLike.congr_fun h N

namespace Coefficients

/-- Оболочка физических тестов, использующая только индексы I. -/
def physicalContractionSpan (alg : Coefficients K P Q S ι) (η : Q → K) (I : Set ι) :
    Submodule K (Matrix S P K →ₗ[K] (Q → K)) :=
  Submodule.span K (Set.range fun i : I ↦ alg.physicalContraction η i.val)

theorem finrank_physicalContractionSpan_le (alg : Coefficients K P Q S ι)
    (η : Q → K) (I : Set ι) :
    finrank K (alg.physicalContractionSpan η I) ≤ I.ncard := by
  classical
  have h := finrank_range_le_card (R := K) (fun i : I ↦ alg.physicalContraction η i.val)
  rw [Set.fintypeCard_eq_ncard] at h
  exact h

end Coefficients

namespace ExactAlgorithm

/-- Все формы N↦tr(NC)η лежат в полной оболочке Qᵢ. -/
theorem trace_separable_mem_physicalContractionSpan (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (C : Matrix P S K) :
    separableMap matrixTracePairing η C ∈
      alg.toCoefficients.physicalContractionSpan η Set.univ := by
  have he : separableMap matrixTracePairing η C =
      ∑ i, alg.toCoefficients.gamma C i • alg.toCoefficients.physicalContraction η i := by
    classical
    ext N q
    have h := congrArg (fun X : Matrix S P K ↦ trace (X * C))
      (alg.physicalContraction_reconstruction η N (Pi.single q 1))
    simpa [separableMap_apply, Coefficients.gamma, traceCoordinates,
      Matrix.sum_mul, trace_sum, Matrix.smul_mul, trace_smul, mul_comm] using h.symm
  rw [he]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨i, Set.mem_univ i⟩, rfl⟩

/-- Для одного d достаточно индексов, содержащих его носитель. -/
theorem conductorMatrix_separable_mem_physicalContractionSpan [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (u : P → K) (θ : Q → K) (I : Set ι) (hI : ∀ i, d.val i ≠ 0 → i ∈ I) :
    separableMap matrixTracePairing θ
      (alg.conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η u)) ∈
      alg.toCoefficients.physicalContractionSpan η I := by
  have he : separableMap matrixTracePairing θ
      (alg.conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η u)) =
      ∑ i, (d.val i * alg.toCoefficients.alpha (vecMulVec θ u) i) •
        alg.toCoefficients.physicalContraction η i := by
    ext N q
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, separableMap_apply,
      matrixTracePairing_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (alg.physicalContraction_weighted_reconstruction η hη d u θ N).symm q
  rw [he]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : d.val i = 0
  · simp [hi]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hI i hi⟩, rfl⟩)

/-- Вся физическая оболочка и все направления Q восстанавливаются на supp D. -/
theorem conductorPhysicalSpace_separable_mem [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (I : Set ι)
    (hI : ∀ d ∈ conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)), ∀ i, d i ≠ 0 → i ∈ I)
    (C : Matrix P S K)
    (hC : C ∈ conductorPhysicalSpace alg.toCoefficients.gamma
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) (θ : Q → K) :
    separableMap matrixTracePairing θ C ∈ alg.toCoefficients.physicalContractionSpan η I := by
  have hh : conductorPhysicalSpace alg.toCoefficients.gamma
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) ≤
      (alg.toCoefficients.physicalContractionSpan η I).comap
        (separableMap matrixTracePairing θ) := by
    rw [alg.conductorPhysicalSpace_eq_span_hyperplane η hη]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨d, u⟩, rfl⟩
    exact alg.conductorMatrix_separable_mem_physicalContractionSpan η hη d u θ I
      (hI d.val d.property)
  exact hh hC

/-- ps+(q−1)e≤ℓ: физическая верхняя оценка насыщенной оболочки. -/
theorem saturated_physical_length_bound [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0) :
    Fintype.card P * Fintype.card S + (Fintype.card Q - 1) * finrank K
      (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
        conductor alg.toCoefficients.gamma.range
          (alg.toCoefficients.alphaOn (coordinateHyperplane η))) ≤ Fintype.card ι := by
  have h := finrank_le_of_separable_maps_and_line (K := K) (U := Matrix S P K)
    (V := Matrix P S K) (Q := Q) matrixTracePairing
    matrixTracePairing_injective
    (conductorPhysicalSpace alg.toCoefficients.gamma
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (alg.toCoefficients.physicalContractionSpan η Set.univ) η hη
    (alg.trace_separable_mem_physicalContractionSpan η)
    (alg.conductorPhysicalSpace_separable_mem η hη Set.univ (by intros; trivial))
  rw [finrank_conductorPhysicalSpace _ alg.gamma_injective, Module.finrank_matrix] at h
  have hh := alg.toCoefficients.finrank_physicalContractionSpan_le η Set.univ
  simp only [Set.ncard_univ] at hh
  simpa only [finrank_self, Nat.mul_one, Nat.card_eq_fintype_card] using h.trans hh

/-- Та же оценка для F коразмерности один, без выбора формы в формулировке. -/
theorem saturated_physical_length_bound_of_hyperplane [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (hF : finrank K F + 1 = Fintype.card Q) :
    Fintype.card P * Fintype.card S + (Fintype.card Q - 1) * finrank K
      (alg.toCoefficients.alphaOn F *
        conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F)) ≤
      Fintype.card ι := by
  obtain ⟨η, hη, rfl⟩ := exists_coordinateHyperplane_of_finrank_add_one F hF
  exact alg.saturated_physical_length_bound η hη

end ExactAlgorithm
end MMRank
