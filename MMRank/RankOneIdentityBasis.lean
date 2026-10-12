import MMRank.RankOneHyperplanes
import MMRank.LinearRankSum

/-! # Минимальная оболочка простых матриц с единицей
Общая линейная часть.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MMRank
open Matrix Module
variable {K Q : Type*} [Field K] [Fintype Q] [DecidableEq Q]

omit [DecidableEq Q] in
/-- Ранг элемента оболочки простых матриц оплачивается размерностью оболочки. -/
theorem matrix_rank_le_finrank_of_rank_one_spanning
    (M : Submodule K (Matrix Q Q K))
    (hs : Submodule.span K {A : M | A.val.rank ≤ 1} = ⊤) (A : M) :
    A.val.rank ≤ finrank K M := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_in_spanning_set (Module.finBasis K M) _ hs
  have he : ∑ i, b.repr A i • (b i).val = A.val := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply]
      using congrArg M.subtype (b.sum_repr A)
  have hr := matrix_rank_weighted_sum_le (fun i ↦ (b i).val) (fun i ↦ b.repr A i)
    1 hb
  rw [he, mul_one] at hr
  exact hr.trans (by simpa using Set.ncard_le_card {i | b.repr A i ≠ 0})

/-- Unital оболочка, порождённая rank1, имеет размерность не меньше размера матриц. -/
theorem card_le_finrank_of_one_mem_rank_one_spanning
    (M : Submodule K (Matrix Q Q K))
    (hs : Submodule.span K {A : M | A.val.rank ≤ 1} = ⊤)
    (h1 : (1 : Matrix Q Q K) ∈ M) : Fintype.card Q ≤ finrank K M := by
  simpa using matrix_rank_le_finrank_of_rank_one_spanning M hs ⟨1, h1⟩

/-- Базис из q простых матриц, выражающий единицу, одновременно диагонализируется.
Обе обратные матрицы даны явно; поле произвольно. -/
theorem rank_one_identity_basis_diagonalization
    (M : Submodule K (Matrix Q Q K)) (b : Basis Q K M)
    (hb : ∀ i, (b i).val.rank ≤ 1) (h1 : (1 : Matrix Q Q K) ∈ M) :
    ∃ X Y : Matrix Q Q K, X * Y = 1 ∧ Y * X = 1 ∧
      ∀ A ∈ M, ∀ a c, a ≠ c → (Y * A * X) a c = 0 := by
  classical
  choose x y hxy using fun i ↦ exists_vecMulVec_of_rank_le_one (b i).val (hb i)
  let c : Q → K := fun i ↦ b.repr ⟨1, h1⟩ i
  let X : Matrix Q Q K := fun a i ↦ c i * x i a
  let Y : Matrix Q Q K := fun i a ↦ y i a
  have he : ∑ i, c i • (b i).val = (1 : Matrix Q Q K) := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply, c]
      using congrArg M.subtype (b.sum_repr ⟨1, h1⟩)
  have hXY : X * Y = 1 := by
    rw [← he]
    ext a d
    simp only [Matrix.mul_apply, X, Y, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hxy i]
    simp [vecMulVec, mul_assoc]
  have hYX : Y * X = 1 := mul_eq_one_comm.mp hXY
  have hterm (i : Q) : c i • (b i).val = X * Matrix.single i i 1 * Y := by
    rw [← hxy i]
    ext a d
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [X, Y, vecMulVec, mul_assoc]
    · intro j _ hj
      rw [Matrix.mul_single_apply_of_ne (1 : K) i i a j hj X]
      exact zero_mul _
    · simp
  have hc (i : Q) : c i ≠ 0 := by
    intro hz
    have hh := congrArg (fun T : Matrix Q Q K ↦ T i i) hYX
    simp [Matrix.mul_apply, X, hz] at hh
  have hdiag (i : Q) (a d : Q) (had : a ≠ d) : (Y * (b i).val * X) a d = 0 := by
    have hh : c i • (Y * (b i).val * X) = Matrix.single i i 1 := by
      calc
        c i • (Y * (b i).val * X) = Y * (c i • (b i).val) * X := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
        _ = Y * (X * Matrix.single i i 1 * Y) * X := by rw [hterm]
        _ = Matrix.single i i 1 := by
          calc
            _ = (Y * X) * Matrix.single i i 1 * (Y * X) := by
              simp only [Matrix.mul_assoc]
            _ = _ := by rw [hYX, Matrix.one_mul, Matrix.mul_one]
    have hh' := congrArg (fun T : Matrix Q Q K ↦ T a d) hh
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.single_apply] at hh'
    have hz : (if i = a ∧ i = d then (1 : K) else 0) = 0 := by
      split_ifs with h
      · exact (had (h.1.symm.trans h.2)).elim
      · rfl
    rw [hz] at hh'
    exact (mul_eq_zero.mp hh').resolve_left (hc i)
  refine ⟨X, Y, hXY, hYX, ?_⟩
  intro A hA a d had
  have heA : ∑ i, b.repr ⟨A, hA⟩ i • (b i).val = A := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply]
      using congrArg M.subtype (b.sum_repr ⟨A, hA⟩)
  rw [← heA, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, hdiag _ a d had, mul_zero, Finset.sum_const_zero]

end MMRank
