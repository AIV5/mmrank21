import MMRank.RankNormalForm
import MMRank.TraceDuality

/-! # Две нормальные формы следовой гиперплоскости матриц порядка2 -/

namespace MMRank
open Matrix Module
variable {K : Type*} [Field K]

/-- Ненулевая матрица порядка2 имеет одну из двух лево-правых нормальных
форм над исходным полем: E₀₀ либо единица. -/
theorem twoByTwo_nonzero_normal_form (N : Matrix (Fin 2) (Fin 2) K) (hN : N ≠ 0) :
    ∃ A B : (Matrix (Fin 2) (Fin 2) K)ˣ,
      (↑A : Matrix (Fin 2) (Fin 2) K) * N * (↑B : Matrix (Fin 2) (Fin 2) K) =
        Matrix.single 0 0 1 ∨
      (↑A : Matrix (Fin 2) (Fin 2) K) * N * (↑B : Matrix (Fin 2) (Fin 2) K) = 1 := by
  have hlo : N.rank ≠ 0 := mt (matrix_rank_eq_zero_iff N).mp hN
  have hhi : N.rank ≤ 2 := by simpa using Matrix.rank_le_card_width N
  have hr : N.rank = 1 ∨ N.rank = 2 := by omega
  rcases hr with hr | hr
  · have hn : ∃ (V U : Matrix (Fin 2) (Fin 2) K) (e : Fin 2 ≃ Fin 1 ⊕ Fin 1),
        IsUnit V ∧ IsUnit U ∧ V * N * U = (fromBlocks 1 0 0 0).submatrix e e := by
      have hh := Matrix.exists_rank_normal_form (R := K) N
      rw [hr] at hh
      exact hh
    obtain ⟨V, U, e, ⟨v, rfl⟩, ⟨u, rfl⟩, he⟩ := hn
    let f : Fin 2 ≃ Fin 1 ⊕ Fin 1 := (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm
    let σ := f.trans e.symm
    let p := matrixPermutationUnit (K := K) σ
    refine ⟨p * v, u * p⁻¹, Or.inl ?_⟩
    change ((↑p : Matrix (Fin 2) (Fin 2) K) * (↑v : Matrix (Fin 2) (Fin 2) K)) * N *
      ((↑u : Matrix (Fin 2) (Fin 2) K) * (↑p⁻¹ : Matrix (Fin 2) (Fin 2) K)) = _
    rw [show ((↑p : Matrix (Fin 2) (Fin 2) K) * (↑v : Matrix (Fin 2) (Fin 2) K)) * N *
      ((↑u : Matrix (Fin 2) (Fin 2) K) * (↑p⁻¹ : Matrix (Fin 2) (Fin 2) K)) =
      (↑p : Matrix (Fin 2) (Fin 2) K) * ((↑v : Matrix (Fin 2) (Fin 2) K) * N *
        (↑u : Matrix (Fin 2) (Fin 2) K)) * (↑p⁻¹ : Matrix (Fin 2) (Fin 2) K) by simp [mul_assoc]]
    rw [matrixPermutationUnit_mul, he, submatrix_submatrix]
    have hef : (e : Fin 2 → Fin 1 ⊕ Fin 1) ∘ σ = f := by ext i; simp [σ]
    rw [hef]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [f, finSumFinEquiv, Fin.addCases, Fin.castLT, Fin.subNat, Matrix.single]
  · have hn : ∃ (V U : Matrix (Fin 2) (Fin 2) K) (e : Fin 2 ≃ Fin 2 ⊕ Fin 0),
        IsUnit V ∧ IsUnit U ∧ V * N * U = (fromBlocks 1 0 0 0).submatrix e e := by
      have hh := Matrix.exists_rank_normal_form (R := K) N
      rw [hr] at hh
      exact hh
    obtain ⟨V, U, e, ⟨v, rfl⟩, ⟨u, rfl⟩, he⟩ := hn
    refine ⟨v, u, Or.inr ?_⟩
    rw [he]
    have hb : (fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 0) (Fin 2 ⊕ Fin 0) K) = 1 := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · simp [Matrix.one_apply]
      all_goals exact Fin.elim0 (by assumption)
    rw [hb]
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]

/-- Трёхмерное пространство тестов 2×2 есть следовая гиперплоскость
с ненулевой нормалью. Не предполагается выбранный базис тестов. -/
theorem exists_twoByTwo_trace_normal (T : Submodule K (Matrix (Fin 2) (Fin 2) K))
    (hT : finrank K T = 3) :
    ∃ N : Matrix (Fin 2) (Fin 2) K, N ≠ 0 ∧ ∀ C, C ∈ T ↔ trace (C * N) = 0 := by
  have htop : T ≠ ⊤ := by
    intro he
    have hh : finrank K T = 4 := by rw [he]; simp [finrank_matrix]
    omega
  obtain ⟨N, hN, hn⟩ := exists_nonzero_trace_annihilator T htop
  let φ := (traceLinearMap (Fin 2) K K).comp (mulRightLinearMap (Fin 2) K N)
  have hφ : φ ≠ 0 := by
    intro hz
    apply hN
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro C
    simpa [φ] using DFunLike.congr_fun hz C
  have he : T = φ.ker := by
    apply Submodule.eq_of_le_of_finrank_eq hn
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    have hm : finrank K (Matrix (Fin 2) (Fin 2) K) = 4 := by simp [finrank_matrix]
    rw [hm] at hh
    omega
  exact ⟨N, hN, fun C ↦ by rw [he]; rfl⟩

end MMRank
