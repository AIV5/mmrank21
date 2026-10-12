import MMRank.PhysicalAtomQuotient

/-! # Остаточное тождество на полном аннуляторе атомных тестов

Следовая запись эквивалентна
Σ W_i ⊗ (V_i T U_i) = T ⊗ I, но не требует TensorProduct. Получение
тождества не зависит от числа атомов или порождённости аннулятора rank1.
-/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I J : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Двойственная средняя свёртка точного алгоритма, во всех размерах. -/
theorem dual_sandwich_trace_identity (alg : ExactAlgorithm K P Q S I)
    (T : Matrix S P K) (X : Matrix Q Q K) :
    ∑ i, trace (X * (alg.V i * T * alg.U i)) • alg.W i = trace X • T := by
  classical
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro C
  have hh := congrArg (fun A : Matrix P S K ↦ trace (A * T))
    (alg.sandwich_trace_identity C X)
  simp only [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul] at hh
  have hcycle (i : I) :
      trace ((alg.U i * X * alg.V i) * T) = trace (X * (alg.V i * T * alg.U i)) := by
    simpa only [Matrix.mul_assoc] using
      (trace_mul_cycle X (alg.V i * T) (alg.U i)).symm
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
  simpa only [hcycle, trace_mul_comm (alg.W _) C, mul_comm] using hh

namespace PhysicalAtom
variable {alg : ExactAlgorithm K P Q S I}

/-- Атомный член зануляется на всём аннуляторе его теста. -/
theorem sandwich_eq_zero_of_trace_test_eq_zero
    (a : alg.PhysicalAtom) {i : I} (hi : i ∈ a.support)
    (T : Matrix S P K) (hT : trace (a.test * T) = 0) :
    alg.V i * T * alg.U i = 0 := by
  classical
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (a.sandwich_mem_test_line hi X)
  calc
    trace (X * (alg.V i * T * alg.U i)) = trace ((alg.U i * X * alg.V i) * T) := by
      simpa only [Matrix.mul_assoc] using
        trace_mul_cycle X (alg.V i * T) (alg.U i)
    _ = 0 := by rw [← hc, Matrix.smul_mul, trace_smul, hT, smul_zero]
    _ = trace (X * 0) := by simp

/-- Внешний выход аннулирует всё пространство удалённых тестов. -/
theorem residual_output_annihilates_testSpan [DecidableEq I]
    (a : J → alg.PhysicalAtom) (G : Finset I)
    (hG : ∀ i, i ∈ G ↔ ∃ j, i ∈ (a j).support)
    (i : {i // i ∉ G}) (C : Matrix P S K) (hC : C ∈ testSpan a) :
    trace (alg.W i.val * C) = 0 := by
  let f : Matrix P S K →ₗ[K] K :=
    (LinearMap.proj i.val).comp alg.toCoefficients.gamma
  have hf : testSpan a ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change alg.toCoefficients.gamma (a j).test i.val = 0
    by_contra hn
    exact i.property ((hG i.val).mpr ⟨j, hn⟩)
  exact hf hC

/-- Полный остаточный контракт после удаления объединения атомов.
Для применения к критическому аннулятору нужна лишь отдельная rank1-оболочка. -/
theorem residual_sandwich_trace_identity [DecidableEq I]
    (a : J → alg.PhysicalAtom) (G : Finset I)
    (hG : ∀ i, i ∈ G ↔ ∃ j, i ∈ (a j).support)
    (T : Matrix S P K) (hT : ∀ j, trace ((a j).test * T) = 0)
    (X : Matrix Q Q K) :
    ∑ i : {i // i ∉ G}, trace (X * (alg.V i.val * T * alg.U i.val)) • alg.W i.val =
      trace X • T := by
  classical
  rw [← alg.dual_sandwich_trace_identity T X]
  symm
  apply Finset.sum_congr_set {i | i ∉ G} _ _
  · intro i hi
    rfl
  · intro i hi
    simp only [Set.mem_ofPred_eq, not_not] at hi
    obtain ⟨j, hj⟩ := (hG i).mp hi
    rw [(a j).sandwich_eq_zero_of_trace_test_eq_zero hj T (hT j)]
    simp

end PhysicalAtom
end MMRank.ExactAlgorithm
