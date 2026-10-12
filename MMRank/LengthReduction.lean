module

public import MMRank.Algorithm
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

@[expose] public section

/-!
# Удаление нулевых слагаемых и доведение длины

Алгоритм длины не больше n приводится к ровно n ненулевым слагаемым
над исходным полем, если все физические пространства ненулевые и pq > 1.
Ни минимальность, ни предварительная нижняя оценка длины не используются.
Операции над алгоритмами выделены над коммутативным полукольцом;
геометрическое существование расщепления — над телом размерности > 1.
-/

namespace MMRank

open Matrix
open scoped BigOperators

variable {K P Q S ι κ : Type*}
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] [Fintype κ]

section Semiring

variable [CommSemiring K]

/-- У каждого слагаемого все три матричных коэффициента ненулевые.
Это не условие ненулевых координат внутри самих матриц. -/
def Coefficients.NonzeroTerms (d : Coefficients K P Q S ι) : Prop :=
  ∀ i, d.U i ≠ 0 ∧ d.V i ≠ 0 ∧ d.W i ≠ 0

namespace ExactAlgorithm

/-- Переиндексация точного алгоритма по биекции. -/
def reindex (d : ExactAlgorithm K P Q S ι) (e : ι ≃ κ) :
    ExactAlgorithm K P Q S κ where
  U j := d.U (e.symm j)
  V j := d.V (e.symm j)
  W j := d.W (e.symm j)
  exact_formula := by
    intro A B
    rw [d.exact_formula A B]
    exact (e.symm.sum_comp _).symm

/-- Переиндексация сохраняет ненулевые коэффициенты. -/
theorem nonzeroTerms_reindex (d : ExactAlgorithm K P Q S ι) (e : ι ≃ κ)
    (h : d.toCoefficients.NonzeroTerms) : (d.reindex e).toCoefficients.NonzeroTerms :=
  fun j ↦ h (e.symm j)

/-- Удаление индексов, у которых хотя бы один из трёх коэффициентов равен нулю.
Число оставшихся слагаемых не увеличивается; они переиндексируются через Fin r. -/
theorem exists_nonzero_reduction (d : ExactAlgorithm K P Q S ι) :
    ∃ r ≤ Fintype.card ι, ∃ e : ExactAlgorithm K P Q S (Fin r),
      e.toCoefficients.NonzeroTerms := by
  classical
  let active : ι → Prop := fun i ↦ d.U i ≠ 0 ∧ d.V i ≠ 0 ∧ d.W i ≠ 0
  let c : ExactAlgorithm K P Q S {i // active i} := {
    U := fun i ↦ d.U i.val
    V := fun i ↦ d.V i.val
    W := fun i ↦ d.W i.val
    exact_formula := by
      intro A B
      rw [d.exact_formula A B]
      apply Finset.sum_congr_set {i | active i}
      · intro i hi
        rfl
      · intro i hi
        simp only [Set.mem_ofPred_eq, active, not_and_or, ne_eq, not_not] at hi
        rcases hi with hu | hv | hw
        · simp [hu]
        · simp [hv]
        · simp [hw]
  }
  refine ⟨Fintype.card {i // active i}, Fintype.card_subtype_le active,
    c.reindex (Fintype.equivFin _), ?_⟩
  exact c.nonzeroTerms_reindex _ (fun i ↦ i.property)

/-- Заменить Uᵢ = u + v двумя слагаемыми с прежними Vᵢ и Wᵢ.
Новый индекс none несёт u; индекс some i несёт v. -/
def split (d : ExactAlgorithm K P Q S ι) [DecidableEq ι]
    (i : ι) (u v : Matrix P Q K) (huv : u + v = d.U i) :
    ExactAlgorithm K P Q S (Option ι) where
  U j := j.elim u (Function.update d.U i v)
  V j := j.elim (d.V i) d.V
  W j := j.elim (d.W i) d.W
  exact_formula := by
    intro A B
    rw [d.exact_formula A B]
    simp only [Coefficients.evaluate, Fintype.sum_option, Option.elim_none, Option.elim_some]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne
      (fun j ↦ (trace (Function.update d.U i v j * A) * trace (d.V j * B)) • d.W j) i]
    simp only [Function.update_self]
    have hrest : (∑ j : {j // j ≠ i},
        (trace (Function.update d.U i v j.val * A) * trace (d.V j.val * B)) • d.W j.val) =
        ∑ j : {j // j ≠ i}, (trace (d.U j.val * A) * trace (d.V j.val * B)) • d.W j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Function.update_of_ne j.property]
    rw [hrest, ← huv, Matrix.add_mul, Matrix.trace_add, add_mul, add_smul, add_assoc]

/-- Если обе части Uᵢ ненулевые, расщепление сохраняет NonzeroTerms. -/
theorem nonzeroTerms_split (d : ExactAlgorithm K P Q S ι) [DecidableEq ι]
    (h : d.toCoefficients.NonzeroTerms) (i : ι) (u v : Matrix P Q K)
    (huv : u + v = d.U i) (hu : u ≠ 0) (hv : v ≠ 0) :
    (d.split i u v huv).toCoefficients.NonzeroTerms := by
  intro j
  cases j with
  | none => exact ⟨hu, (h i).2⟩
  | some j =>
    change Function.update d.U i v j ≠ 0 ∧ d.V j ≠ 0 ∧ d.W j ≠ 0
    by_cases hj : j = i
    · subst j
      simpa using And.intro hv (h i).2
    · simpa [Function.update_of_ne hj] using h j

end ExactAlgorithm

end Semiring

/-- В пространстве размерности > 1 ненулевой вектор есть сумма двух ненулевых.
Размерность кардинальная: допускаются и бесконечномерные пространства. -/
theorem exists_nonzero_add_nonzero {D E : Type*} [DivisionRing D]
    [AddCommGroup E] [Module D E] (hdim : 1 < Module.rank D E)
    (x : E) (hx : x ≠ 0) : ∃ u v : E, u ≠ 0 ∧ v ≠ 0 ∧ u + v = x := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_rank hdim hx
  have hy0 : y ≠ 0 := by simpa using hy.ne_zero (1 : Fin 2)
  have hyx : y ≠ x := by
    simpa using hy.injective.ne (by decide : (1 : Fin 2) ≠ 0)
  exact ⟨y, x - y, hy0, sub_ne_zero.mpr hyx.symm, add_sub_cancel _ _⟩

namespace ExactAlgorithm

section Extension

variable [CommSemiring K] [Nontrivial K] [Nonempty P] [Nonempty Q] [Nonempty S]

/-- Умножение в ненулевых размерах не имеет алгоритма с пустым набором слагаемых. -/
theorem index_nonempty (d : ExactAlgorithm K P Q S ι) : Nonempty ι := by
  classical
  by_contra h
  have : IsEmpty ι := not_nonempty_iff.mp h
  let p : P := Classical.arbitrary P
  let q : Q := Classical.arbitrary Q
  let s : S := Classical.arbitrary S
  have he := congrArg (fun M : Matrix S P K ↦ M s p)
    (d.exact_formula (Matrix.single q p 1) (Matrix.single s q 1))
  simp [Coefficients.evaluate] at he

/-- Индуктивное увеличение длины при явно заданной возможности расщепления.
В полевом результате ниже эта возможность доказана, а не постулирована. -/
theorem exists_nonzero_extension (d : ExactAlgorithm K P Q S ι)
    (hd : d.toCoefficients.NonzeroTerms)
    (hsplit : ∀ x : Matrix P Q K, x ≠ 0 →
      ∃ u v : Matrix P Q K, u ≠ 0 ∧ v ≠ 0 ∧ u + v = x)
    (n : ℕ) (hn : Fintype.card ι ≤ n) :
    ∃ e : ExactAlgorithm K P Q S (Fin n), e.toCoefficients.NonzeroTerms := by
  classical
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨d.reindex (Fintype.equivFin ι), d.nonzeroTerms_reindex _ hd⟩
  | succ n hn ih =>
    obtain ⟨e, he⟩ := ih
    have : Nonempty (Fin n) := e.index_nonempty
    let i : Fin n := Classical.arbitrary (Fin n)
    obtain ⟨u, v, hu, hv, huv⟩ := hsplit (e.U i) (he i).1
    let f := e.split i u v huv
    let eqv : Option (Fin n) ≃ Fin (n + 1) :=
      Fintype.equivFinOfCardEq (by simp)
    exact ⟨f.reindex eqv, f.nonzeroTerms_reindex eqv (e.nonzeroTerms_split he i u v huv hu hv)⟩

end Extension

variable [Field K] [Nonempty P] [Nonempty Q] [Nonempty S]

/-- Доведение до любой большей длины: удалить нулевые слагаемые, затем расщеплять.
Все коэффициенты остаются над исходным полем. -/
theorem exists_nonzero_length (d : ExactAlgorithm K P Q S ι)
    (hdim : 1 < Fintype.card P * Fintype.card Q) (n : ℕ) (hn : Fintype.card ι ≤ n) :
    ∃ e : ExactAlgorithm K P Q S (Fin n), e.toCoefficients.NonzeroTerms := by
  obtain ⟨r, hr, e, he⟩ := d.exists_nonzero_reduction
  apply e.exists_nonzero_extension he ?_ n (by simpa using hr.trans hn)
  intro x hx
  apply exists_nonzero_add_nonzero (D := K) ?_ x hx
  apply Module.one_lt_rank_of_one_lt_finrank
  simpa [Module.finrank_matrix] using hdim

end ExactAlgorithm

end MMRank
