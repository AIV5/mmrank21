module

public import MMRank.ReciprocalLine
public import MMRank.PointWords

@[expose] public section

/-! # Физический выходной тест точечного слова

Нормировка фиксирует масштаб общего направления Uᵢη. Никакое
прямосуммовое разложение по носителю не предполагается.
-/

namespace MMRank
open Matrix Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

namespace Coefficients

omit [Fintype S] [Fintype ι] in
theorem alpha_hyperplaneInput_apply (alg : Coefficients K P Q S ι)
    (η : Q → K) (u : P → K) (i : ι) :
    alg.alpha (hyperplaneInput η u).val i = u ⬝ᵥ (alg.U i *ᵥ η) := by
  simp [Coefficients.alpha, traceCoordinates, hyperplaneInput_val,
    mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

end Coefficients

namespace ExactAlgorithm
variable [Nonempty Q]

/-- Для точечного слова весь подъём C_d является скалярным семейством
его единственного физического прообраза. Произвольное F, без единицы. -/
theorem conductorMatrix_eq_smul_of_pointWord
    (alg : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (C : Matrix P S K) (hp : IsPointWord (alg.toCoefficients.alphaOn F) (alg.toCoefficients.gamma C))
    (i : ι) (hi : alg.toCoefficients.gamma C i ≠ 0)
    (A : matricesKilling (P := P) F) :
    alg.conductorMatrix F ⟨alg.toCoefficients.gamma C, hp.mem_conductor ⟨C, rfl⟩⟩ A =
      alg.toCoefficients.alpha A.val i • C := by
  apply alg.gamma_injective
  rw [alg.gamma_conductorMatrix, map_smul]
  exact hp.mul_eq_coordinate hi (Submodule.mem_map.mpr ⟨A, A.property, rfl⟩)

/-- Нормированное точечное слово имеет тест ранга один C=p⊗s,
и все Uᵢη на его носителе равны одному ненулевому p. -/
theorem pointWord_test_factors
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (C : Matrix P S K)
    (hp : IsPointWord (alg.toCoefficients.alphaOn (coordinateHyperplane η))
      (alg.toCoefficients.gamma C)) :
    ∃ p : P → K, ∃ s : S → K, p ≠ 0 ∧ s ≠ 0 ∧ C = vecMulVec p s ∧
      ∀ i, alg.toCoefficients.gamma C i ≠ 0 → alg.U i *ᵥ η = p := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, alg.toCoefficients.gamma C i ≠ 0 := by
    simpa [funext_iff] using hp.1
  let p := alg.U i *ᵥ η
  have he (j : ι) (hj : alg.toCoefficients.gamma C j ≠ 0) : alg.U j *ᵥ η = p := by
    ext k
    have hh := (isPointWord_iff_constant_on_support _ _).mp hp |>.2
      (alg.toCoefficients.alpha (hyperplaneInput η (Pi.single k 1)).val)
      (Submodule.mem_map.mpr ⟨hyperplaneInput η (Pi.single k 1),
        (hyperplaneInput η (Pi.single k 1)).property, rfl⟩) j i hj hi
    rw [Coefficients.alpha_hyperplaneInput_apply, Coefficients.alpha_hyperplaneInput_apply] at hh
    simpa only [single_dotProduct, one_mul] using hh
  have hp0 : p ≠ 0 := by
    obtain ⟨A, hA, hα⟩ := h1
    obtain ⟨u, hu⟩ := hyperplaneInput_surjective η hη ⟨A, hA⟩
    have hh : alg.toCoefficients.alpha (hyperplaneInput η u).val i = 1 := by
      rw [hu]; exact congrFun hα i
    rw [Coefficients.alpha_hyperplaneInput_apply] at hh
    intro hz
    change u ⬝ᵥ p = 1 at hh
    simp [hz] at hh
  have hc (u : P → K) :
      alg.conductorMatrix (coordinateHyperplane η)
        ⟨alg.toCoefficients.gamma C, hp.mem_conductor ⟨C, rfl⟩⟩ (hyperplaneInput η u) =
        (u ⬝ᵥ p) • C := by
    simpa only [Coefficients.alpha_hyperplaneInput_apply] using
      alg.conductorMatrix_eq_smul_of_pointWord _ C hp i hi (hyperplaneInput η u)
  obtain ⟨s, hs⟩ := exists_outer_of_dot_reciprocity p hp0 C (by
    intro u v
    have hh := alg.conductorMatrix_hyperplane_reciprocity η hη
      ⟨alg.toCoefficients.gamma C, hp.mem_conductor ⟨C, rfl⟩⟩ v u
    simpa only [hc, vecMul_smul] using hh)
  refine ⟨p, s, hp0, ?_, hs, he⟩
  intro hz
  apply hp.1
  have hC : C = 0 := by ext j k; simp [hs, hz, vecMulVec]
  rw [hC, map_zero]

end ExactAlgorithm
end MMRank
