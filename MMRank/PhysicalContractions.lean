module

public import MMRank.PhysicalConductor

@[expose] public section

/-! # Билинейные физические тесты Qᵢ и два тождества восстановления

Qᵢ(N,z)=z Vᵢ N Uᵢ η при правом действии. Сначала храним Qᵢ(N,·)
как координаты линейной формы на Q. Все физические размеры произвольны.
-/

namespace MMRank

open Matrix Module
open scoped BigOperators

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

namespace Coefficients

/-- Линейное N ↦ Vᵢ N Uᵢ η, то есть координаты формы Qᵢ(N,·). -/
def physicalContraction (alg : Coefficients K P Q S ι) (η : Q → K) (i : ι) :
    Matrix S P K →ₗ[K] (Q → K) :=
  (alg.V i).mulVecLin.comp ((mulVecBilin K K).flip ((alg.U i) *ᵥ η))

omit [Fintype ι] in
@[simp] theorem physicalContraction_apply (alg : Coefficients K P Q S ι)
    (η : Q → K) (i : ι) (N : Matrix S P K) :
    alg.physicalContraction η i N = (alg.V i) *ᵥ (N *ᵥ ((alg.U i) *ᵥ η)) := rfl

omit [Fintype ι] in
/-- На простой матрице тест раскладывается в два исходных коэффициента. -/
theorem physicalContraction_rankOne (alg : Coefficients K P Q S ι)
    (η : Q → K) (i : ι) (γ : S → K) (u : P → K) (z : Q → K) :
    z ⬝ᵥ alg.physicalContraction η i (vecMulVec γ u) =
      alg.alpha (vecMulVec η u) i * alg.beta (vecMulVec γ z) i := by
  simp only [physicalContraction_apply, Coefficients.alpha, Coefficients.beta,
    traceCoordinates, LinearMap.coe_mk, AddHom.coe_mk, mul_vecMulVec, trace_vecMulVec]
  rw [vecMulVec_mulVec, op_smul_eq_smul, mulVec_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm u, dotProduct_comm z]

end Coefficients

namespace ExactAlgorithm

/-- Первый физический закон: Σ Qᵢ(N,z)Wᵢ=(z·η)N. -/
theorem physicalContraction_reconstruction (alg : ExactAlgorithm K P Q S ι)
    (η : Q → K) (N : Matrix S P K) (z : Q → K) :
    ∑ i, (z ⬝ᵥ alg.toCoefficients.physicalContraction η i N) • alg.W i =
      (z ⬝ᵥ η) • N := by
  classical
  let L : Matrix S P K →ₗ[K] Matrix S P K :=
    ∑ i, ((dotProductBilin K K z).comp
      (alg.toCoefficients.physicalContraction η i)).smulRight (alg.W i)
  have h : L = (z ⬝ᵥ η) • LinearMap.id := by
    apply Matrix.ext_linearMap
    intro s p
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, L, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.id_apply]
    change (∑ i, (z ⬝ᵥ alg.toCoefficients.physicalContraction η i
      (Matrix.single s p 1)) • alg.W i) = (z ⬝ᵥ η) • Matrix.single s p 1
    rw [Matrix.single_eq_single_vecMulVec_single]
    simp_rw [Coefficients.physicalContraction_rankOne]
    have hh := alg.exact_formula (vecMulVec η (Pi.single p 1))
      (vecMulVec (Pi.single s 1) z)
    simpa only [Coefficients.evaluate, Coefficients.alpha, Coefficients.beta,
      traceCoordinates, LinearMap.coe_mk, AddHom.coe_mk, vecMulVec_mul_vecMulVec,
      vecMulVec_smul] using hh.symm
  simpa only [L, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, dotProductBilin,
    LinearMap.coe_mk, AddHom.coe_mk] using DFunLike.congr_fun h N

/-- Взвешенное восстановление на простой выходной матрице. -/
theorem physicalContraction_weighted_rankOne [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (u v : P → K) (γ : S → K) (θ z : Q → K) :
    ∑ i, (d.val i * alg.toCoefficients.alpha (vecMulVec θ u) i) *
      (z ⬝ᵥ alg.toCoefficients.physicalContraction η i (vecMulVec γ v)) =
      trace (vecMulVec γ v * alg.conductorMatrix (coordinateHyperplane η) d
        (hyperplaneInput η u)) * (z ⬝ᵥ θ) := by
  let C := alg.conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η v)
  have hc (i : ι) : trace (alg.W i * C) =
      alg.toCoefficients.alpha (vecMulVec η v) i * d.val i :=
    congrFun (alg.gamma_conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η v)) i
  calc
    _ = trace (vecMulVec γ z * vecMulVec θ u * C) := by
      rw [trace_mul_comm (vecMulVec γ z * vecMulVec θ u), ← Matrix.mul_assoc,
        alg.trace_identity]
      apply Finset.sum_congr rfl
      intro i _
      rw [Coefficients.physicalContraction_rankOne, hc]
      simp only [Coefficients.alpha, Coefficients.beta, traceCoordinates,
        LinearMap.coe_mk, AddHom.coe_mk]
      ring
    _ = _ := by
      simp only [C, vecMulVec_mul, vecMul_vecMulVec, smul_vecMul,
        trace_vecMulVec, dotProduct_smul, smul_eq_mul]
      rw [alg.conductorMatrix_hyperplane_reciprocity η hη d v u]
      exact mul_comm _ _

/-- Второй физический закон, со всеми выходами N, а не только простыми матрицами. -/
theorem physicalContraction_weighted_reconstruction [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (u : P → K) (θ : Q → K) (N : Matrix S P K) :
    ∑ i, (d.val i * alg.toCoefficients.alpha (vecMulVec θ u) i) •
      alg.toCoefficients.physicalContraction η i N =
      trace (N * alg.conductorMatrix (coordinateHyperplane η) d
        (hyperplaneInput η u)) • θ := by
  classical
  let C := alg.conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η u)
  let L : Matrix S P K →ₗ[K] (Q → K) :=
    ∑ i, (d.val i * alg.toCoefficients.alpha (vecMulVec θ u) i) •
      alg.toCoefficients.physicalContraction η i
  let R : Matrix S P K →ₗ[K] (Q → K) :=
    ((traceLinearMap S K K).comp (mulRightLinearMap S K C)).smulRight θ
  have h : L = R := by
    apply Matrix.ext_linearMap
    intro s p
    apply LinearMap.ext_ring
    ext q
    change L (Matrix.single s p 1) q = R (Matrix.single s p 1) q
    have hh := alg.physicalContraction_weighted_rankOne η hη d u
      (Pi.single p 1) (Pi.single s 1) θ (Pi.single q 1)
    simpa only [L, R, C,
      LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, single_dotProduct, one_mul,
      LinearMap.smulRight_apply, LinearMap.comp_apply, traceLinearMap_apply,
      mulRightLinearMap_apply, Matrix.single_eq_single_vecMulVec_single] using hh
  simpa only [L, R, C, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, traceLinearMap_apply,
    mulRightLinearMap_apply] using DFunLike.congr_fun h N

end ExactAlgorithm
end MMRank
