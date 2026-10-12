import MMRank.PointFreeCollinear

/-! # Физические точечные тесты при смене гиперплоскости и калибровки -/
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Нормировка превращает коллинеарность на носителе в точечность.
Слово не обязано лежать в образе γ; размеры и поле произвольны. -/
theorem isPointWord_of_collinear_support (alg : ExactAlgorithm K P Q S I)
    (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (w : I → K) (hw : w ≠ 0)
    (hc : ∀ i j, w i ≠ 0 → w j ≠ 0 → ∀ a b,
      (alg.U i *ᵥ η) a * (alg.U j *ᵥ η) b =
      (alg.U i *ᵥ η) b * (alg.U j *ᵥ η) a) :
    IsPointWord (alg.toCoefficients.alphaOn (coordinateHyperplane η)) w := by
  obtain ⟨u, hu⟩ := alg.exists_normalizing_row η hη h1
  apply (isPointWord_iff_constant_on_support _ _).mpr
  refine ⟨hw, ?_⟩
  rintro m ⟨A, hA, rfl⟩ i j hi hj
  have he := eq_of_collinear_of_dotProduct_eq_one u (alg.U i *ᵥ η)
    (alg.U j *ᵥ η) (hu i) (hu j) (hc i j hi hj)
  obtain ⟨x, hx⟩ := hyperplaneInput_surjective η hη ⟨A, hA⟩
  have hx' := congrArg Subtype.val hx
  change (hyperplaneInput η x).val = A at hx'
  rw [← hx', Coefficients.alpha_hyperplaneInput_apply,
    Coefficients.alpha_hyperplaneInput_apply, he]

/-- Фиксированный физический класс даёт точечность при любой новой
нормированной гиперплоскости; общность нового η не нужна. -/
theorem isPointWord_of_fixedColumn_support (alg : ExactAlgorithm K P Q S I)
    (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (w : I → K) (hw : w ≠ 0) (p : P → K)
    (hc : ∀ i, w i ≠ 0 → alg.U i ∈ fixedColumnSpace (Q := Q) p) :
    IsPointWord (alg.toCoefficients.alphaOn (coordinateHyperplane η)) w := by
  apply alg.isPointWord_of_collinear_support η hη h1 w hw
  intro i j hi hj a b
  obtain ⟨v, hv⟩ := hc i hi
  obtain ⟨v', hv'⟩ := hc j hj
  change vecMulVec p v = alg.U i at hv
  change vecMulVec p v' = alg.U j at hv'
  rw [← hv, ← hv', vecMulVec_mulVec, vecMulVec_mulVec]
  simp only [Pi.smul_apply, op_smul_eq_mul]
  ring

/-- Обратимые масштабы сохраняют точный носитель каждого физического теста. -/
theorem gamma_rescale_support (alg : ExactAlgorithm K P Q S I)
    (u : I → Kˣ) (C : Matrix P S K) :
    {i | (alg.rescale u).toCoefficients.gamma C i ≠ 0} =
      {i | alg.toCoefficients.gamma C i ≠ 0} := by
  ext i
  simp [rescale, Coefficients.gamma_rescale, Units.ne_zero]

end MMRank.ExactAlgorithm
