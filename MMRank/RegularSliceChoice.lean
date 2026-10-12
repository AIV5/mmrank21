module

public import MMRank.RegularSupportedSlice
public import MMRank.RectangularTestChart
public import MMRank.RegularMatrixPencil

@[expose] public section

/-! # Независимая пара тестов с регулярным первым тестом

Точная квадратная карта
позволяет выбрать полный носитель и определить нескалярный оператор.
Физические размеры, размер квадратной карты и характеристика произвольны.
-/

namespace MMRank
open Matrix Module
open scoped Classical

/-- Регулярное пространство размерности хотя бы два в точной квадратной
карте даёт пару тестов с полным первым носителем и нескалярным оператором.
Совместимость карты с левым действием заменяет выбор специальных тестов. -/
theorem exists_regular_slice_pair
    {K n P S I : Type*} [Field K] [Infinite K]
    [Fintype n] [DecidableEq n] [Fintype P] [Fintype S] [Finite I]
    (T : Submodule K (Matrix P S K))
    (j : Matrix n n K →ₗ[K] Matrix P S K) (L : Matrix n P K)
    (hj : Function.Injective j) (hT : T ≤ j.range)
    (hdim : 2 ≤ finrank K T) (hrank : ∀ C, (j C).rank = C.rank)
    (haction : ∀ H C, L * j (H * C) = H * (L * j C))
    (γ : Matrix P S K →ₗ[K] (I → K))
    (hγ : ∀ i, ∃ C ∈ T, γ C i ≠ 0)
    (hreg : ∃ C ∈ T, C.rank = Fintype.card n) :
    ∃ C ∈ T, ∃ D ∈ T, ∃ H : Matrix n n K,
      C.rank = Fintype.card n ∧ (∀ i, γ C i ≠ 0) ∧
      L * D = H * (L * C) ∧ (∀ a : K, H ≠ a • 1) ∧
      ∀ a : K, D - a • C ≠ 0 := by
  classical
  let R := T.comap j
  let γR : R →ₗ[K] (I → K) := γ.comp (j.comp R.subtype)
  have hγR (i : I) : ∃ A : R, γR A i ≠ 0 := by
    obtain ⟨C, hC, hCi⟩ := hγ i
    obtain ⟨A, rfl⟩ := hT hC
    exact ⟨⟨A, hC⟩, hCi⟩
  have hregR : ∃ A : R, IsUnit A.val := by
    obtain ⟨C, hC, hr⟩ := hreg
    obtain ⟨A, rfl⟩ := hT hC
    refine ⟨⟨A, hC⟩, (matrix_isUnit_iff_rank_eq_card A).mpr ?_⟩
    exact (hrank A).symm.trans hr
  obtain ⟨C, hCu, hCc⟩ := exists_isUnit_slice_with_coordinates R γR hγR hregR
  have hdR : 2 ≤ finrank K R := by
    change 2 ≤ finrank K (T.comap j)
    rw [finrank_comap_of_injective_of_le_range j hj T hT]
    exact hdim
  obtain ⟨D, hD, hDC⟩ : ∃ D ∈ R, D ∉ Submodule.span K {C.val} := by
    by_contra hn
    have hle : R ≤ Submodule.span K {C.val} := by
      intro D hD
      by_contra hDC
      exact hn ⟨D, hD, hDC⟩
    have hm := Submodule.finrank_mono hle
    have hs : finrank K (Submodule.span K {C.val}) ≤ 1 := by
      simpa using finrank_span_le_card ({C.val} : Set (Matrix n n K))
    omega
  have hDne (a : K) : D ≠ a • C.val := by
    intro he
    exact hDC (Submodule.mem_span_singleton.mpr ⟨a, he.symm⟩)
  let H := D * C.val⁻¹
  have hHC : H * C.val = D :=
    Matrix.nonsing_inv_mul_cancel_right C.val D ((Matrix.isUnit_iff_isUnit_det _).mp hCu)
  have hH (a : K) : H ≠ a • 1 := by
    intro he
    apply hDne a
    calc
      D = H * C.val := hHC.symm
      _ = (a • 1) * C.val := by rw [he]
      _ = a • C.val := by rw [Matrix.smul_mul, Matrix.one_mul]
  refine ⟨j C.val, C.property, j D, hD, H, ?_, hCc, ?_, hH, ?_⟩
  · exact (hrank C.val).trans (Matrix.rank_of_isUnit C.val hCu)
  · calc
      L * j D = L * j (H * C.val) := by rw [hHC]
      _ = H * (L * j C.val) := haction H C.val
  · intro a hz
    apply hDne a
    apply hj
    simpa only [map_smul] using sub_eq_zero.mp hz

end MMRank
