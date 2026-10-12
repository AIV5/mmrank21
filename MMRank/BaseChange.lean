module

public import MMRank.LengthReduction
public import Mathlib.LinearAlgebra.Matrix.Bilinear

@[expose] public section

/-!
# Перенос данного алгоритма по гомоморфизму коэффициентов

Точность проверяется на матричных единицах и потому переносится на все входы
нового полукольца. Для сохранения ненулевых коэффициентов нужна инъективность.
Множество слагаемых не меняется. Равенство минимальных рангов не утверждается.
-/

namespace MMRank

open Matrix
open scoped BigOperators

variable {K L P Q S ι : Type*} [CommSemiring K] [CommSemiring L]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

namespace Coefficients

/-- Билинейное отображение, вычисляемое заданными коэффициентами. -/
def evaluateBilinear (d : Coefficients K P Q S ι) :
    Matrix Q P K →ₗ[K] Matrix S Q K →ₗ[K] Matrix S P K where
  toFun A := {
    toFun := d.evaluate A
    map_add' := by
      intro B C
      simp [evaluate, Matrix.mul_add, Matrix.trace_add, mul_add, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro r B
      simp [evaluate, Matrix.mul_smul, Matrix.trace_smul, Finset.smul_sum,
        smul_smul, smul_eq_mul, mul_left_comm]
  }
  map_add' := by
    intro A C
    apply LinearMap.ext
    intro B
    change d.evaluate (A + C) B = d.evaluate A B + d.evaluate C B
    simp [evaluate, Matrix.mul_add, Matrix.trace_add, add_mul, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r A
    apply LinearMap.ext
    intro B
    change d.evaluate (r • A) B = r • d.evaluate A B
    simp [evaluate, Matrix.mul_smul, Matrix.trace_smul, Finset.smul_sum,
      smul_smul, smul_eq_mul, mul_assoc]

/-- Для точности достаточно проверить все пары матричных единиц. -/
theorem isExact_iff_on_single (d : Coefficients K P Q S ι)
    [DecidableEq P] [DecidableEq Q] [DecidableEq S] :
    d.IsExact ↔ ∀ (q : Q) (p : P) (s : S) (q' : Q),
      Matrix.single s q' (1 : K) * Matrix.single q p (1 : K) =
        d.evaluate (Matrix.single q p 1) (Matrix.single s q' 1) := by
  constructor
  · intro h q p s q'
    exact h _ _
  · intro h
    have he : (mulLinearMap K).flip = d.evaluateBilinear := by
      apply Matrix.ext_linearMap
      intro q p
      apply LinearMap.ext_ring
      apply Matrix.ext_linearMap
      intro s q'
      apply LinearMap.ext_ring
      exact h q p s q'
    intro A B
    exact congrArg (fun f : Matrix Q P K →ₗ[K] Matrix S Q K →ₗ[K] Matrix S P K ↦ f A B) he

/-- Покомпонентный перенос коэффициентов без изменения индексов. -/
def map (d : Coefficients K P Q S ι) (f : K →+* L) : Coefficients L P Q S ι where
  U i := (d.U i).map f
  V i := (d.V i).map f
  W i := (d.W i).map f

/-- Вычисление на перенесённых входах коммутирует с переносом выхода. -/
theorem map_evaluate (d : Coefficients K P Q S ι) (f : K →+* L)
    (A : Matrix Q P K) (B : Matrix S Q K) :
    (d.evaluate A B).map f = (d.map f).evaluate (A.map f) (B.map f) := by
  ext s p
  simp [evaluate, map, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, ← Matrix.map_mul, ← AddMonoidHom.map_trace]

/-- Точность переносится на все входы над L, не только на входы из образа K. -/
theorem IsExact.map {d : Coefficients K P Q S ι} (h : d.IsExact) (f : K →+* L) :
    (d.map f).IsExact := by
  classical
  apply (isExact_iff_on_single _).mpr
  intro q p s q'
  have hm := congrArg (fun M : Matrix S P K ↦ M.map f)
    (h (Matrix.single q p 1) (Matrix.single s q' 1))
  simpa only [Matrix.map_mul, map_evaluate, Matrix.map_single, map_one] using hm

private theorem map_eq_zero_iff {m n : Type*} (M : Matrix m n K)
    (f : K →+* L) (hf : Function.Injective f) : M.map f = 0 ↔ M = 0 := by
  rw [← Matrix.map_zero f (map_zero f)]
  exact (Matrix.map_injective hf).eq_iff

omit [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] in
/-- Ненулевость всех коэффициентов сохраняется и отражается вложением. -/
theorem nonzeroTerms_map_iff (d : Coefficients K P Q S ι) (f : K →+* L)
    (hf : Function.Injective f) : (d.map f).NonzeroTerms ↔ d.NonzeroTerms := by
  simp only [NonzeroTerms, map, ne_eq, map_eq_zero_iff _ f hf]

end Coefficients

/-- Перенос точного алгоритма с сохранением его множества слагаемых. -/
def ExactAlgorithm.map (d : ExactAlgorithm K P Q S ι) (f : K →+* L) :
    ExactAlgorithm L P Q S ι where
  toCoefficients := d.toCoefficients.map f
  exact_formula := d.exact_formula.map f

/-- Доведение длины над исходным полем и перенос в любое поле по вложению.
Ни бесконечность, ни алгебраическая замкнутость не нужны. -/
theorem ExactAlgorithm.exists_nonzero_length_map
    {K L : Type*} [Field K] [Field L]
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (d : ExactAlgorithm K P Q S ι) (f : K →+* L)
    (hdim : 1 < Fintype.card P * Fintype.card Q) (n : ℕ) (hn : Fintype.card ι ≤ n) :
    ∃ e : ExactAlgorithm L P Q S (Fin n), e.toCoefficients.NonzeroTerms := by
  obtain ⟨e, he⟩ := d.exists_nonzero_length hdim n hn
  exact ⟨e.map f, (Coefficients.nonzeroTerms_map_iff _ f f.injective).mpr he⟩

end MMRank
