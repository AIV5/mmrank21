import MMRank.AdjacentPointClasses
import MMRank.PointWordPhysical
import MMRank.PointClassBudget
import MMRank.PointTestColumnCore

/-! # Физический атом без выбора общей гиперплоскости -/
namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Ненулевой простой физический тест с минимальным носителем.
Его средний базис и точные локальные тождества выводятся из алгоритма.
Нормировка и размер3 в определение не входят. -/
structure PhysicalAtom (alg : ExactAlgorithm K P Q S I) where
  first : P → K
  last : S → K
  first_ne_zero : first ≠ 0
  last_ne_zero : last ≠ 0
  card_support : {i | alg.toCoefficients.gamma (vecMulVec first last) i ≠ 0}.ncard = Fintype.card Q

namespace PhysicalAtom
variable {alg : ExactAlgorithm K P Q S I}

def test (a : PhysicalAtom alg) : Matrix P S K := vecMulVec a.first a.last
def support (a : PhysicalAtom alg) : Set I := {i | alg.toCoefficients.gamma a.test i ≠ 0}

/-- Минимальный носитель даёт средний базис с точной факторизацией U. -/
theorem exists_basis (a : PhysicalAtom alg) :
    ∃ b : Basis a.support K (Q → K), ∀ i : a.support,
      alg.U i.val = vecMulVec a.first (b i) :=
  alg.exists_basis_of_minimal_gamma_support a.support a.first a.first_ne_zero a.last a.last_ne_zero
    (by intro i hi; exact not_ne_iff.mp hi) a.card_support

theorem U_mem (a : PhysicalAtom alg) {i : I} (hi : i ∈ a.support) :
    alg.U i ∈ fixedColumnSpace (Q := Q) a.first := by
  obtain ⟨b, hb⟩ := a.exists_basis
  exact ⟨b ⟨i, hi⟩, (hb ⟨i, hi⟩).symm⟩

theorem V_mem (a : PhysicalAtom alg) {i : I} (hi : i ∈ a.support) :
    alg.V i ∈ matricesInto (S := Q) (Submodule.span K {a.last}) :=
  alg.V_mem_row_class_of_minimal_support a.support a.first a.first_ne_zero a.last a.last_ne_zero
    (by intro i hi; exact not_ne_iff.mp hi) a.card_support ⟨i, hi⟩

/-- Взвешенная двойственность внутри атома, включая диагональ. -/
theorem weighted_product (a : PhysicalAtom alg) (i j : a.support) :
    alg.toCoefficients.gamma a.test i.val • (alg.U j.val * alg.V i.val) =
      (if j = i then (1 : K) else 0) • a.test := by
  classical
  obtain ⟨b, hb⟩ := a.exists_basis
  exact alg.weighted_UV_of_test_basis a.support a.first a.first_ne_zero a.last
    (by intro i hi; exact not_ne_iff.mp hi) b hb i j

theorem test_ne_zero (a : PhysicalAtom alg) : a.test ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a.first i ≠ 0 := by simpa [funext_iff] using a.first_ne_zero
  obtain ⟨j, hj⟩ : ∃ j, a.last j ≠ 0 := by simpa [funext_iff] using a.last_ne_zero
  intro hz
  exact mul_ne_zero hi hj (congrFun (congrFun hz i) j)

theorem product_ne_zero (a : PhysicalAtom alg) {i : I} (hi : i ∈ a.support) :
    alg.U i * alg.V i ≠ 0 := by
  have hh := a.weighted_product ⟨i, hi⟩ ⟨i, hi⟩
  simp only [ite_true, one_smul] at hh
  intro hz
  exact a.test_ne_zero (by simpa only [hz, smul_zero] using hh.symm)

/-- На каждом атомном индексе оба соседних ранга равны1. -/
theorem ranks_eq_one (a : PhysicalAtom alg) {i : I} (hi : i ∈ a.support) :
    (alg.U i).rank = 1 ∧ (alg.V i).rank = 1 := by
  obtain ⟨b, hb⟩ := a.exists_basis
  have hr : (alg.U i).rank ≤ 1 := by rw [hb ⟨i, hi⟩]; exact rank_vecMulVec_le _ _
  have hn : (alg.U i).rank ≠ 0 := by
    intro hz
    have hu := (matrix_rank_eq_zero_iff _).mp hz
    exact a.product_ne_zero hi (by rw [hu, Matrix.zero_mul])
  refine ⟨by omega, ?_⟩
  exact alg.V_rank_eq_one_of_test_basis a.support a.first a.first_ne_zero a.last a.last_ne_zero
    (by intro i hi; exact not_ne_iff.mp hi) b hb ⟨i, hi⟩

/-- Точечный тест при общности столбцового ядра сразу даёт атом.
Полный пакет классов, соседних рангов и локальных тождеств для этого
конструктора не нужен; они выводятся из минимального носителя отдельно. -/
theorem exists_of_pointTest_column_generic
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (hg : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (C : Matrix P S K)
    (hc : IsPointWord (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (alg.toCoefficients.gamma C)) :
    ∃ a : PhysicalAtom alg, a.test = C := by
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p, s, hp0, hs0, he, hu⟩ := alg.pointWord_test_factors η hη h1 C hc
  let G : Set I := {i | alg.toCoefficients.gamma C i ≠ 0}
  have hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0 := by
    intro i hi
    rw [← he]
    exact not_ne_iff.mp hi
  have hspan := alg.span_eq_fixedColumnSpace_of_column_generic η hη hg G p s hs0 hG hu
  have hcard : G.ncard = Fintype.card Q := by
    have hlo := alg.card_le_of_gamma_supported_outer G p hp0 s hs0 hG
    have hhi := (alg.point_class_capacity hp hq hs hl p hp0 G hspan.le).1
    omega
  refine ⟨⟨p, s, hp0, hs0, ?_⟩, he.symm⟩
  simpa only [← he] using hcard

end PhysicalAtom
end MMRank.ExactAlgorithm
