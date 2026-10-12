import MMRank.GenericSupportedTest
import MMRank.PointClassBudget

/-! # Коллинеарные группы без точечных тестов -/

namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [Field K] [Fintype P]

/-- Один нормирующий функционал устраняет скалярную неоднозначность
коллинеарных векторов. -/
theorem eq_of_collinear_of_dotProduct_eq_one (u p q : P → K)
    (hp : u ⬝ᵥ p = 1) (hq : u ⬝ᵥ q = 1)
    (hc : ∀ a b, p a * q b = p b * q a) : p = q := by
  ext a
  have h : p a * (u ⬝ᵥ q) = q a * (u ⬝ᵥ p) := by
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    calc
      p a * (u b * q b) = u b * (p a * q b) := by ring
      _ = u b * (p b * q a) := by rw [hc a b]
      _ = q a * (u b * p b) := by ring
  simpa only [hp, hq, mul_one] using h

namespace ExactAlgorithm
variable [Fintype Q] [Fintype S] [Fintype I]

/-- На коллинеарной нормированной группе любой ненулевой поддержанный
тест точечен; поэтому отсутствие точек зануляет всё сечение. -/
theorem section_eq_bot_of_noPointWords_of_collinear
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (G : Set I)
    (hn : HasNoPointWords (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (coordinateSection K alg.toCoefficients.gamma.range G))
    (hc : ∀ (i j : G) a b, (alg.U i *ᵥ η) a * (alg.U j *ᵥ η) b =
      (alg.U i *ᵥ η) b * (alg.U j *ᵥ η) a) :
    coordinateSection K alg.toCoefficients.gamma.range G = ⊥ := by
  obtain ⟨u, hu⟩ := alg.exists_normalizing_row η hη h1
  apply eq_bot_iff.mpr
  intro w hw
  change w = 0
  by_contra hw0
  apply hn w hw
  apply (isPointWord_iff_constant_on_support _ w).mpr
  refine ⟨hw0, ?_⟩
  rintro m ⟨A, hA, rfl⟩ i j hi hj
  have hiG : i ∈ G := by by_contra h; exact hi (hw.2 i h)
  have hjG : j ∈ G := by by_contra h; exact hj (hw.2 j h)
  obtain ⟨x, hx⟩ := hyperplaneInput_surjective η hη ⟨A, hA⟩
  have he := eq_of_collinear_of_dotProduct_eq_one u (alg.U i *ᵥ η)
    (alg.U j *ᵥ η) (hu i) (hu j) (hc ⟨i, hiG⟩ ⟨j, hjG⟩)
  have hx' := congrArg Subtype.val hx
  change (hyperplaneInput η x).val = A at hx'
  rw [← hx', Coefficients.alpha_hyperplaneInput_apply,
    Coefficients.alpha_hyperplaneInput_apply, he]

/-- В первом фиксированном классе без точек при333 длины≤20
остаются не более двух индексов, а не трёх. -/
theorem point_free_fixedColumn_card_le_two
    (alg : ExactAlgorithm K P Q S I)
    (hP : Fintype.card P = 3) (hQ : Fintype.card Q = 3) (hS : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (G : Set I) (p : P → K) (hp : p ≠ 0)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p)
    (hn : HasNoPointWords (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (coordinateSection K alg.toCoefficients.gamma.range G)) : G.ncard ≤ 2 := by
  have hz := alg.section_eq_bot_of_noPointWords_of_collinear η hη h1 G hn (by
    intro i j a b
    obtain ⟨v, hv⟩ := hspan (Submodule.subset_span ⟨i.val, i.property, rfl⟩)
    obtain ⟨w, hw⟩ := hspan (Submodule.subset_span ⟨j.val, j.property, rfl⟩)
    change vecMulVec p v = alg.U i at hv
    change vecMulVec p w = alg.U j at hw
    rw [← hv, ← hw, vecMulVec_mulVec, vecMulVec_mulVec]
    simp only [Pi.smul_apply, op_smul_eq_mul]
    ring)
  have hb := alg.point_class_budget hP hQ hS p hp G hspan
  dsimp only at hb
  rw [hz, finrank_bot] at hb
  have hh := G.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hh
  omega

end ExactAlgorithm
end MMRank
