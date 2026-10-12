import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Точный билинейный алгоритм

Правое действие на строках: матрица `Matrix P Q K` задаёт отображение
`(P → K) →ₗ[K] (Q → K)` посредством `vecMulLinear`.
Входы имеют типы `A : Matrix Q P K`, `B : Matrix S Q K`, `C : Matrix P S K`.
Коэффициентный цикл — UVW; входной — CBA.

Основной результат этого модуля — эквивалентность точной билинейной формулы
и её трилинейной записи. Оценок длины алгоритма здесь нет.
-/

namespace MMRank

open Matrix
open scoped BigOperators

variable {K P Q S ι : Type*}

/-- Коэффициенты длины `Fintype.card ι`: U : P → Q, V : Q → S, W : S → P.
Здесь P, Q, S — множества координат, а физические пространства — P → K и т. д. -/
structure Coefficients (K P Q S ι : Type*) where
  U : ι → Matrix P Q K
  V : ι → Matrix Q S K
  W : ι → Matrix S P K

section RowAction

variable [Semiring K] [Fintype P] [Fintype Q]

/-- Стандартная композиция LinearMap выражает сначала U, затем V как V.comp U. -/
theorem rowLinear_mul (U : Matrix P Q K) (V : Matrix Q S K) :
    (U * V).vecMulLinear = V.vecMulLinear.comp U.vecMulLinear := by
  exact LinearMap.ext fun x ↦ (Matrix.vecMul_vecMul x U V).symm

end RowAction

variable [CommSemiring K] [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

namespace Coefficients

/-- Выход билинейной формулы на входах A : Q → P и B : S → Q. -/
def evaluate (d : Coefficients K P Q S ι) (A : Matrix Q P K) (B : Matrix S Q K) :
    Matrix S P K :=
  ∑ i, (trace (d.U i * A) * trace (d.V i * B)) • d.W i

/-- Точность: формула вычисляет BA для всех входов. -/
def IsExact (d : Coefficients K P Q S ι) : Prop :=
  ∀ (A : Matrix Q P K) (B : Matrix S Q K), B * A = d.evaluate A B

/-- Эквивалентная трилинейная формула с входным циклом CBA. -/
def TraceIdentity (d : Coefficients K P Q S ι) : Prop :=
  ∀ (A : Matrix Q P K) (B : Matrix S Q K) (C : Matrix P S K),
    trace (C * B * A) =
      ∑ i, trace (d.U i * A) * trace (d.V i * B) * trace (d.W i * C)

/-- След от вычисленного выхода раскрывается в правую часть трилинейной формулы. -/
theorem trace_evaluate (d : Coefficients K P Q S ι)
    (A : Matrix Q P K) (B : Matrix S Q K) (C : Matrix P S K) :
    trace (C * d.evaluate A B) =
      ∑ i, trace (d.U i * A) * trace (d.V i * B) * trace (d.W i * C) := by
  simp only [evaluate, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm C]

/-- Эквивалентность двух формул над коммутативным полукольцом, включая нулевые размеры. -/
theorem isExact_iff_traceIdentity
    (d : Coefficients K P Q S ι) : d.IsExact ↔ d.TraceIdentity := by
  constructor
  · intro h A B C
    rw [Matrix.mul_assoc, h A B, trace_evaluate]
  · intro h A B
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro C
    rw [trace_evaluate, ← Matrix.mul_assoc]
    exact h A B C

end Coefficients

/-- Точный алгоритм с конечным набором слагаемых; минимальность и ненулевые
коэффициенты не предполагаются. Для длины ℓ можно взять ι = Fin ℓ. -/
structure ExactAlgorithm (K P Q S ι : Type*) [CommSemiring K]
    [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]
    extends Coefficients K P Q S ι where
  exact_formula : toCoefficients.IsExact

/-- Каждый точный алгоритм удовлетворяет трилинейной формуле. -/
theorem ExactAlgorithm.trace_identity (d : ExactAlgorithm K P Q S ι) :
    d.toCoefficients.TraceIdentity :=
  d.toCoefficients.isExact_iff_traceIdentity.mp d.exact_formula

/-- Циклический сдвиг коэффициентов сохраняет точность и меняет формат P,Q,S на Q,S,P. -/
def ExactAlgorithm.rotate (d : ExactAlgorithm K P Q S ι) : ExactAlgorithm K Q S P ι where
  U := d.V
  V := d.W
  W := d.U
  exact_formula := (Coefficients.isExact_iff_traceIdentity _).mpr (by
    intro A B C
    change trace (C * B * A) = ∑ i,
      trace (d.V i * A) * trace (d.W i * B) * trace (d.U i * C)
    calc
      trace (C * B * A) = trace (B * A * C) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm C (B * A)]
      _ = ∑ i, trace (d.U i * C) * trace (d.V i * A) * trace (d.W i * B) :=
        d.trace_identity C A B
      _ = _ := by simp only [mul_comm, mul_assoc])

end MMRank
