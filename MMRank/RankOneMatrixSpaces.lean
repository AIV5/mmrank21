module

public import MMRank.GCDMatrixFactorization

@[expose] public section

/-! # Общий фактор пространства матриц ранга не больше одного

Произвольное поле и конечные прямоугольные размеры. Нулевое пространство
и пустые множества индексов допускаются.
-/

namespace MMRank
open Matrix Module

/-- Прямоугольная версия критерия нулевого внешнего произведения:
типы строк и столбцов независимы, конечность не нужна. -/
theorem outerProduct_eq_zero_iff {R m n : Type*} [MulZeroClass R] [NoZeroDivisors R]
    (x : m → R) (y : n → R) : vecMulVec x y = 0 ↔ x = 0 ∨ y = 0 := by
  simp only [← Matrix.ext_iff, vecMulVec_apply, Matrix.zero_apply, mul_eq_zero,
    funext_iff, Pi.zero_apply, forall_or_left, forall_or_right]

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

theorem exists_vecMulVec_of_rank_le_one (A : Matrix m n K) (hA : A.rank ≤ 1) :
    ∃ x : m → K, ∃ y : n → K, vecMulVec x y = A := by
  obtain ⟨x, y, h⟩ := (exists_outerProduct_iff_minors_eq_zero A).mpr
    (fun i k j l ↦ sub_eq_zero.mp (minor_two_eq_zero_of_rank_le_one A hA i k j l))
  exact ⟨x, y, by ext i j; exact (h i j).symm⟩

omit [Fintype m] [Fintype n] in
/-- Нулевые двумерные внешние произведения с ненулевым x дают кратность x. -/
theorem exists_smul_of_cross_products_zero (x u : m → K) (hx : x ≠ 0)
    (h : ∀ i j, x i * u j - x j * u i = 0) : ∃ a : K, u = a • x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by simpa [funext_iff] using hx
  refine ⟨u i / x i, ?_⟩
  ext j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hi).mpr
  linear_combination h i j

/-- Если сумма двух простых матриц имеет ранг≤1, они разделяют один фактор. -/
theorem outer_sum_rank_le_one_factors (x : m → K) (y : n → K)
    (hx : x ≠ 0) (hy : y ≠ 0) (u : m → K) (v : n → K)
    (hr : (vecMulVec x y + vecMulVec u v).rank ≤ 1) :
    (∃ a : K, u = a • x) ∨ (∃ b : K, v = b • y) := by
  have hm := minor_two_eq_zero_of_rank_le_one _ hr
  have hprod (i j : m) (k l : n) :
      (x i * u j - x j * u i) * (y k * v l - y l * v k) = 0 := by
    have hh := hm i j k l
    simp only [Matrix.add_apply, vecMulVec_apply] at hh
    linear_combination hh
  by_cases hl : ∀ i j, x i * u j - x j * u i = 0
  · exact Or.inl (exists_smul_of_cross_products_zero x u hx hl)
  · push Not at hl
    obtain ⟨i, j, hij⟩ := hl
    exact Or.inr (exists_smul_of_cross_products_zero y v hy
      (fun k l ↦ (mul_eq_zero.mp (hprod i j k l)).resolve_left hij))

/-- Пространство ранга≤1 имеет общий левый либо общий правый фактор. -/
theorem rank_le_one_space_common_factor (T : Submodule K (Matrix m n K))
    (hr : ∀ A ∈ T, A.rank ≤ 1) :
    (∃ x : m → K, ∀ A ∈ T, ∃ y : n → K, vecMulVec x y = A) ∨
    (∃ y : n → K, ∀ A ∈ T, ∃ x : m → K, vecMulVec x y = A) := by
  by_cases hT : T = ⊥
  · left; refine ⟨0, ?_⟩; intro A hA
    have hz : A = 0 := by simpa [hT] using hA
    exact ⟨0, by simp [hz]⟩
  obtain ⟨A, hA, hA0⟩ := (Submodule.ne_bot_iff T).mp hT
  obtain ⟨x, y, hxy⟩ := exists_vecMulVec_of_rank_le_one A (hr A hA)
  have hx : x ≠ 0 := by intro h; apply hA0; rw [← hxy, h]; simp
  have hy : y ≠ 0 := by intro h; apply hA0; rw [← hxy, h]; ext i j; simp [vecMulVec]
  let L := (vecMulVecBilin K K x : (n → K) →ₗ[K] Matrix m n K).range
  let R := ((vecMulVecBilin K K).flip y : (m → K) →ₗ[K] Matrix m n K).range
  have hLR (B : Matrix m n K) (hB : B ∈ T) : B ∈ L ∨ B ∈ R := by
    obtain ⟨u, v, huv⟩ := exists_vecMulVec_of_rank_le_one B (hr B hB)
    have hs : (vecMulVec x y + vecMulVec u v).rank ≤ 1 := by
      rw [hxy, huv]; exact hr _ (T.add_mem hA hB)
    rcases outer_sum_rank_le_one_factors x y hx hy u v hs with ⟨a, ha⟩ | ⟨b, hb⟩
    · left; refine ⟨a • v, ?_⟩
      change vecMulVec x (a • v) = B
      rw [← huv, ha]; ext i j; simp [vecMulVec, mul_left_comm, mul_assoc]
    · right; refine ⟨b • u, ?_⟩
      change vecMulVec (b • u) y = B
      rw [← huv, hb]; ext i j; simp [vecMulVec, mul_left_comm, mul_assoc]
  have hc : T ≤ L ∨ T ≤ R := AddSubgroupClass.subset_union.mp hLR
  rcases hc with hL | hR
  · exact Or.inl ⟨x, fun B hB ↦ hL hB⟩
  · exact Or.inr ⟨y, fun B hB ↦ hR hB⟩

end MMRank
