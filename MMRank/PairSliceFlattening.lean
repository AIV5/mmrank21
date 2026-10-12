module

public import MMRank.LinearRankSum
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Развёртка по парам срезов и ганкелев вход 2×3

Для d срезов простой член даёт ранг≤d−1. Используются все упорядоченные
пары; повторные и нулевые компоненты не влияют на ранг. Нижняя оценка
ганкелева умножения затем получается без определителей и ограничений
на характеристику. Срезы — линейные отображения, не физические матрицы U.
-/

namespace MMRank
open Module
variable {K V W J : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- (x_i) ↦ (P_i x_j − P_j x_i) по всем парам индексов. -/
def pairSliceLinear (P : J → V →ₗ[K] W) : (J → V) →ₗ[K] (J → J → W) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (P i).comp (LinearMap.proj j) - (P j).comp (LinearMap.proj i)

@[simp] theorem pairSliceLinear_apply (P : J → V →ₗ[K] W) (x : J → V) (i j : J) :
    pairSliceLinear P x i j = P i (x j) - P j (x i) := rfl

theorem scalar_pairSlice_rank_le [Fintype J] (p : J → K) :
    finrank K (pairSliceLinear (fun i ↦ p i • (LinearMap.id : K →ₗ[K] K))).range ≤
      Fintype.card J - 1 := by
  let f := pairSliceLinear (fun i ↦ p i • (LinearMap.id : K →ₗ[K] K))
  change finrank K f.range ≤ _
  by_cases hp : p = 0
  · have hf : f = 0 := by ext x i j; simp [f, hp]
    rw [hf, LinearMap.range_zero, finrank_bot]
    exact Nat.zero_le _
  · have hk : p ∈ f.ker := by
      change f p = 0
      ext i j; simp [f, mul_comm]
    have hd := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hk)
    rw [finrank_span_singleton hp] at hd
    have hr := f.finrank_range_add_finrank_ker
    simp only [Module.finrank_pi] at hr
    omega

end MMRank
