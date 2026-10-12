import MMRank.RankOneMatrixSpaces
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Общий вектор, различающий направления конечного семейства матриц -/

namespace MMRank
open Matrix MvPolynomial

/-- Конечное семейство ненулевых многочленов одновременно не обращается
в нуль над бесконечной областью. Число переменных произвольно. -/
theorem exists_eval_all_ne_zero {K σ I : Type*} [CommRing K] [IsDomain K]
    [Infinite K] [Fintype I] (f : I → MvPolynomial σ K) (hf : ∀ i, f i ≠ 0) :
    ∃ x : σ → K, ∀ i, eval x (f i) ≠ 0 := by
  classical
  have hp : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by simpa using hf)
  have he : ∃ x : σ → K, eval x (∏ i, f i) ≠ 0 := by
    by_contra! h
    exact hp (MvPolynomial.funext (by simpa using h))
  obtain ⟨x, hx⟩ := he
  refine ⟨x, ?_⟩
  simpa only [map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] using hx

variable {K P Q I : Type*} [Field K] [Fintype Q]

/-- Коллинеарность значений в η обнаруживает только тождественную
поточечную коллинеарность операторов; нулевые значения допускаются. -/
def MatrixDirectionGeneric (U : I → Matrix P Q K) (η : Q → K) : Prop :=
  ∀ i j, (∀ a b, (U i *ᵥ η) a * (U j *ᵥ η) b =
    (U i *ᵥ η) b * (U j *ᵥ η) a) →
    ∀ x a b, (U i *ᵥ x) a * (U j *ᵥ x) b = (U i *ᵥ x) b * (U j *ᵥ x) a

/-- Полиномиальная координата Aη. -/
noncomputable def matrixVectorPolynomial (A : Matrix P Q K) (a : P) : MvPolynomial Q K :=
  ∑ q, C (A a q) * X q

theorem matrixVectorPolynomial_eval (A : Matrix P Q K) (a : P) (x : Q → K) :
    eval x (matrixVectorPolynomial A a) = (A *ᵥ x) a := by
  simp [matrixVectorPolynomial, mulVec, dotProduct]

omit [Fintype Q] in
/-- Конечные ненулевые полиномы объединяются в один открытый свидетель. -/
theorem polynomial_open_finset {J : Type*} [Fintype J]
    (f : J → MvPolynomial Q K) (hf : ∀ j, f j ≠ 0) :
    ∃ g : MvPolynomial Q K, g ≠ 0 ∧ ∀ η, eval η g ≠ 0 → ∀ j, eval η (f j) ≠ 0 := by
  classical
  refine ⟨∏ j, f j, Finset.prod_ne_zero_iff.mpr (by simpa using hf), ?_⟩
  intro η hη
  simpa only [map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] using hη

end MMRank
