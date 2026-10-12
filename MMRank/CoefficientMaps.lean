import MMRank.Algorithm
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Коэффициентные отображения α, β, γ

Общая конструкция traceCoordinates даёт линейное отображение в функции на индексах.
Для точного алгоритма инъективность α следует из точности и одной непустой
физической размерности; β и γ получаются циклическим сдвигом того же доказательства.
Здесь рассматриваются полные образы, ещё не ограничения A_F и B_F.
-/

namespace MMRank

open Matrix Module

variable {K P Q S ι : Type*}

section Semiring

variable [CommSemiring K]

/-- Следовые координаты по семейству матриц; конечность множества индексов не нужна. -/
def traceCoordinates [Fintype P] [Fintype Q] (T : ι → Matrix P Q K) :
    Matrix Q P K →ₗ[K] (ι → K) where
  toFun A i := trace (T i * A)
  map_add' A B := by ext i; simp [Matrix.mul_add]
  map_smul' r A := by ext i; simp [Matrix.mul_smul]

namespace Coefficients

/-- α(A)ᵢ = tr(UᵢA), где A : Q → P при правом действии. -/
def alpha [Fintype P] [Fintype Q] (d : Coefficients K P Q S ι) :
    Matrix Q P K →ₗ[K] (ι → K) := traceCoordinates d.U

/-- β(B)ᵢ = tr(VᵢB), где B : S → Q при правом действии. -/
def beta [Fintype Q] [Fintype S] (d : Coefficients K P Q S ι) :
    Matrix S Q K →ₗ[K] (ι → K) := traceCoordinates d.V

/-- γ(C)ᵢ = tr(WᵢC), где C : P → S при правом действии. -/
def gamma [Fintype S] [Fintype P] (d : Coefficients K P Q S ι) :
    Matrix P S K →ₗ[K] (ι → K) := traceCoordinates d.W

end Coefficients

/-- Координата i входит в носитель полного образа ровно при Tᵢ ≠ 0.
Это не утверждение о ненулевости каждой координаты каждого элемента образа. -/
theorem traceCoordinates_coord_nonzero_iff [Fintype P] [Fintype Q]
    (T : ι → Matrix P Q K) (i : ι) :
    (∃ a ∈ (traceCoordinates T).range, a i ≠ 0) ↔ T i ≠ 0 := by
  constructor
  · rintro ⟨a, ⟨A, rfl⟩, ha⟩ hT
    apply ha
    change trace (T i * A) = 0
    simp [hT]
  · intro hi
    have hx : ∃ A, trace (T i * A) ≠ 0 := by
      by_contra! h
      apply hi
      apply Matrix.ext_iff_trace_mul_right.mpr
      intro A
      simpa using h A
    obtain ⟨A, hA⟩ := hx
    exact ⟨traceCoordinates T A, ⟨A, rfl⟩, hA⟩

namespace ExactAlgorithm

variable [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Точность различает входы A по α(A), если есть хотя бы одна строка тестового B. -/
theorem alpha_injective [Nonempty S] (d : ExactAlgorithm K P Q S ι) :
    Function.Injective d.toCoefficients.alpha := by
  classical
  intro A A' h
  have ht (i : ι) : trace (d.U i * A) = trace (d.U i * A') := congrFun h i
  have hm (B : Matrix S Q K) : B * A = B * A' := by
    rw [d.exact_formula, d.exact_formula]
    simp only [Coefficients.evaluate, ht]
  ext q p
  let s : S := Classical.arbitrary S
  have he := congrArg (fun M : Matrix S P K ↦ M s p) (hm (Matrix.single s q 1))
  simpa using he

/-- Инъективность β — тот же результат после циклического сдвига. -/
theorem beta_injective [Nonempty P] (d : ExactAlgorithm K P Q S ι) :
    Function.Injective d.toCoefficients.beta :=
  d.rotate.alpha_injective

/-- Инъективность γ — тот же результат после двух циклических сдвигов. -/
theorem gamma_injective [Nonempty Q] (d : ExactAlgorithm K P Q S ι) :
    Function.Injective d.toCoefficients.gamma :=
  d.rotate.rotate.alpha_injective

end ExactAlgorithm

end Semiring

namespace ExactAlgorithm

variable [Field K] [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Размерность полного первого образа равна pq. -/
theorem finrank_range_alpha [Nonempty S] (d : ExactAlgorithm K P Q S ι) :
    finrank K d.toCoefficients.alpha.range = Fintype.card P * Fintype.card Q := by
  rw [LinearMap.finrank_range_of_inj d.alpha_injective]
  simp [Module.finrank_matrix, Nat.mul_comm]

/-- Размерность полного третьего образа равна sp. -/
theorem finrank_range_gamma [Nonempty Q] (d : ExactAlgorithm K P Q S ι) :
    finrank K d.toCoefficients.gamma.range = Fintype.card S * Fintype.card P :=
  d.rotate.rotate.finrank_range_alpha

end ExactAlgorithm

end MMRank
