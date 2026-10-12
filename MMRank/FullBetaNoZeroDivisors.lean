import MMRank.RestrictedCoefficients
import MMRank.AlgorithmGeneralPosition

/-!
# Полное второе коэффициентное пространство и роль гиперплоскости

При FA=0 условие rank A=codim F эквивалентно ker A=F. Поэтому порождение
активными Vᵢ исключает невидимый второй вход B во всём пространстве.
Для гиперплоскости каждый ненулевой A, зануляющий F, удовлетворяет критерию.
При c>1 это не утверждается для ненулевых входов меньшего ранга.
-/

namespace MMRank

open Module

section Linear

variable {K X Y : Type*} [DivisionRing K]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y]

/-- Ненулевое отображение, зануляющее гиперплоскость, имеет в точности это ядро. -/
theorem ker_eq_of_hyperplane_le (F : Submodule K X) (f : X →ₗ[K] Y)
    (hF : F ≤ f.ker) (hdim : finrank K F + 1 = finrank K X) (hf : f ≠ 0) :
    f.ker = F := by
  have h := f.finrank_range_add_finrank_ker
  have hle := Submodule.finrank_mono hF
  have hr : 0 < finrank K f.range := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hf (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
  apply (Submodule.eq_of_le_of_finrank_eq hF _).symm
  omega

end Linear

section Matrices

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S]

namespace Coefficients

omit [Field K] in
/-- Порождение активными Vᵢ исключает любой ненулевой второй вход B.
Точность алгоритма, бесконечность поля и конечность множества слагаемых здесь не нужны. -/
theorem full_beta_input_eq_zero_of_active_span [CommSemiring K] [NoZeroDivisors K]
    (d : Coefficients K P Q S ι)
    (A : Matrix Q P K)
    (hspan : Submodule.span K (d.V '' {i | Matrix.trace (d.U i * A) ≠ 0}) = ⊤)
    (B : Matrix S Q K) (hab : d.alpha A * d.beta B = 0) : B = 0 := by
  apply eq_zero_of_weighted_trace_products d.V (d.alpha A) hspan B
  intro i
  exact congrFun hab i

/-- Для гиперплоскости получаем отсутствие делителей нуля A_F × im β,
а не только A_F × B_F. Условное утверждение не требует бесконечного поля. -/
theorem hyperplane_full_beta_no_zero_divisors (d : Coefficients K P Q S ι)
    (F : Submodule K (Q → K)) (hF : finrank K F + 1 = Fintype.card Q)
    (hspan : ∀ A : Matrix Q P K, A.vecMulLinear.ker ≤ F →
      Submodule.span K (d.V '' {i | Matrix.trace (d.U i * A) ≠ 0}) = ⊤)
    {a b : ι → K} (ha : a ∈ d.alphaOn F) (hb : b ∈ d.beta.range)
    (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨A, hA, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨B, rfl⟩ := hb
  by_cases hzero : A = 0
  · left; simp [hzero]
  · right
    have hn : A.vecMulLinear ≠ 0 := by
      intro hz
      apply hzero
      apply rowLinearEquiv.injective
      simpa using hz
    have hker := ker_eq_of_hyperplane_le F A.vecMulLinear
      ((mem_matricesKilling F A).mp hA) (by simpa using hF) hn
    have hB := d.full_beta_input_eq_zero_of_active_span A (hspan A hker.le) B hab
    simp [hB]

end Coefficients

namespace ExactAlgorithm

variable [Fintype ι]

end ExactAlgorithm

end Matrices

end MMRank
