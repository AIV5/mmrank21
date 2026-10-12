module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-! # Квадратичная форма, зануляющая гиперплоскость

Делимость на линейную форму
выводится поляризацией, включая характеристику2 и произвольную размерность.
-/
namespace MMRank
open Module QuadraticMap
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Форма, нулевая на ядре ненулевой линейной формы, есть её произведение
на другую линейную форму. Ни конечномерность, ни деление на2 не нужны. -/
theorem quadratic_eq_linMulLin_of_zero_on_kernel (Q : QuadraticForm K V)
    (φ : Module.Dual K V) (hφ : φ ≠ 0) (hz : ∀ x, φ x = 0 → Q x = 0) :
    ∃ ψ : Module.Dual K V, Q = linMulLin φ ψ := by
  classical
  obtain ⟨t,ht⟩ := LinearMap.surjective hφ 1
  refine ⟨Q.polarBilin t - Q t • φ, ?_⟩
  ext x
  have hzero : Q (x - φ x • t) = 0 := hz _ (by simp [ht])
  have he := QuadraticMap.map_add Q (x - φ x • t) (φ x • t)
  simp only [sub_add_cancel, hzero, QuadraticMap.map_smul, polar_smul_right,
    polar_sub_left, polar_smul_left, polar_self, smul_eq_mul, nsmul_eq_mul] at he
  simp only [linMulLin_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    polarBilin_apply_apply, smul_eq_mul]
  rw [polar_comm Q t x]
  linear_combination he

end MMRank
