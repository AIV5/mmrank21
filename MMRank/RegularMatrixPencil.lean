module

public import MMRank.RankOneMatrixSpaces
public import MMRank.ReciprocalColumnSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-! # Регулярность матричного пучка с полными совместными носителями -/

namespace MMRank
open Matrix Module
variable {K P S : Type*} [Field K] [Fintype P] [Fintype S]

omit [Fintype P] [Fintype S] in
/-- Квадратная матрица обратима ровно при полном ранге, включая размер0. -/
theorem matrix_isUnit_iff_rank_eq_card {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : IsUnit A ↔ A.rank = Fintype.card n := by
  refine ⟨Matrix.rank_of_isUnit A, ?_⟩
  intro hr
  apply (mulVec_surjective_iff_isUnit).mp
  change Function.Surjective A.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa only [Matrix.rank, Module.finrank_pi] using hr

omit [Fintype P] in
/-- Общий первый фактор ограничивает совместную колонковую оболочку одной
прямой. Само пространство матриц может иметь произвольную размерность. -/
theorem matrixColumnSpan_le_span_of_common_factor
    (T : Submodule K (Matrix P S K)) (p : P → K)
    (h : ∀ C ∈ T, ∃ s : S → K, vecMulVec p s = C) :
    matrixColumnSpan T ≤ Submodule.span K {p} := by
  apply iSup_le
  intro C
  obtain ⟨s, hs⟩ := h C.val C.property
  rintro _ ⟨v, rfl⟩
  change v ᵥ* C.val.transpose ∈ _
  rw [← hs, transpose_vecMulVec, vecMul_vecMulVec]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton p))

/-- Если всё пространство имеет ранг≤1, общий столбцовый либо строковый
носитель имеет размерность≤1. Произвольные размеры и поле. -/
theorem rank_le_one_space_joint_span
    (T : Submodule K (Matrix P S K)) (hr : ∀ C ∈ T, C.rank ≤ 1) :
    finrank K (matrixColumnSpan T) ≤ 1 ∨
      finrank K (matrixColumnSpan (T.map (transposeLinearEquiv P S K K).toLinearMap)) ≤ 1 := by
  rcases rank_le_one_space_common_factor T hr with ⟨p,hp⟩ | ⟨s,hs⟩
  · exact Or.inl ((Submodule.finrank_mono (matrixColumnSpan_le_span_of_common_factor T p hp)).trans
      (finrank_span_le_card ({p} : Set (P → K)) |>.trans (by simp)))
  · right
    apply (Submodule.finrank_mono (matrixColumnSpan_le_span_of_common_factor _ s ?_)).trans
      (finrank_span_le_card ({s} : Set (S → K)) |>.trans (by simp))
    rintro _ ⟨C,hC,rfl⟩
    obtain ⟨p, hp⟩ := hs C hC
    exact ⟨p, by change vecMulVec s p = C.transpose; rw [← hp, transpose_vecMulVec]⟩

/-- Два совместных носителя размерности≥2 вынуждают наличие теста
ранга≥2. Размеры матриц и размерность пространства произвольны. -/
theorem exists_rank_ge_two_of_joint_spans (T : Submodule K (Matrix P S K))
    (hc : 2 ≤ finrank K (matrixColumnSpan T))
    (hr : 2 ≤ finrank K (matrixColumnSpan
      (T.map (transposeLinearEquiv P S K K).toLinearMap))) :
    ∃ C ∈ T, 2 ≤ C.rank := by
  by_contra hn
  push Not at hn
  have hlow (C : Matrix P S K) (hC : C ∈ T) : C.rank ≤ 1 := by
    have hh := hn C hC
    omega
  rcases rank_le_one_space_joint_span T hlow with hh | hh <;> omega

end MMRank
