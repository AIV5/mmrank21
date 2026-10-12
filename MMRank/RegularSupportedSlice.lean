module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import MMRank.UniqueRelationFactors

@[expose] public section

/-! # Регулярный поддержанный тест с полным носителем

Общий выбор на одной прямой
сохраняет регулярность и избегает нулей всех конечных координат.
Размер матриц и характеристика поля произвольны.
-/

namespace MMRank
open Matrix Module
open scoped Classical

/-- Над бесконечным полем регулярное матричное подпространство с полным
координатным носителем содержит обратимую матрицу без нулевых координат.
Независимость координатных форм и размерность подпространства не нужны. -/
theorem exists_isUnit_slice_with_coordinates
    {K n I : Type*} [Field K] [Infinite K] [Fintype n] [DecidableEq n] [Finite I]
    (T : Submodule K (Matrix n n K)) (γ : T →ₗ[K] (I → K))
    (hγ : ∀ i, ∃ A : T, γ A i ≠ 0) (hreg : ∃ A : T, IsUnit A.val) :
    ∃ A : T, IsUnit A.val ∧ ∀ i, γ A i ≠ 0 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨D, hD⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun i ↦ (LinearMap.proj i).comp γ) hγ
  obtain ⟨C₀, hC₀⟩ := hreg
  let p : Polynomial K :=
    ((Polynomial.X : Polynomial K) • D.val.map Polynomial.C +
      C₀.val.map Polynomial.C).det
  have hp_eval (z : K) : p.eval z = (z • D.val + C₀.val).det := by
    change (Polynomial.evalRingHom z) _ = _
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hp0 : p.eval 0 ≠ 0 := by
    rw [hp_eval]
    rw [zero_smul, zero_add]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hC₀).ne_zero
  have hp : p ≠ 0 := by
    intro hz
    apply hp0
    rw [hz, Polynomial.eval_zero]
  let f (i : I) : Polynomial K :=
    Polynomial.C (γ C₀ i) + Polynomial.C (γ D i) * Polynomial.X
  have hf (i : I) : f i ≠ 0 := by
    intro hz
    have h := congrArg (fun q : Polynomial K ↦ q.coeff 1) hz
    exact hD i (by simpa [f, Polynomial.coeff_C_mul_X] using h)
  have hprod : p * ∏ i, f i ≠ 0 :=
    mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr (by simpa using hf))
  obtain ⟨z, hz⟩ : ∃ z : K, (p * ∏ i, f i).eval z ≠ 0 := by
    by_contra! h
    exact hprod (Polynomial.zero_of_eval_zero _ h)
  have hh : (z • D.val + C₀.val).det ≠ 0 ∧ ∀ i, γ C₀ i + γ D i * z ≠ 0 := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, hp_eval, mul_ne_zero_iff,
      Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const, f] using hz
  refine ⟨z • D + C₀, (Matrix.isUnit_iff_isUnit_det _).mpr ?_, ?_⟩
  · exact isUnit_iff_ne_zero.mpr hh.1
  · intro i
    simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, add_comm, mul_comm] using hh.2 i

namespace ExactAlgorithm

variable {K P Q S I N : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Fintype N]

/-- Координаты двух поддержанных тестов с общей операторной связью
задают отношения вторых коэффициентов на носителе. -/
theorem supported_slice_operator_relation_mem_kernel
    (alg : ExactAlgorithm K P Q S I) (G : Set I)
    (C D : Matrix P S K)
    (hC : C ∈ alg.toCoefficients.supportedTests G)
    (hD : D ∈ alg.toCoefficients.supportedTests G)
    (L : Matrix N P K) (H : Matrix N N K)
    (hLD : L * D = H * (L * C)) (x : N) (q : Q) :
    (fun i : G ↦ alg.toCoefficients.gamma D i * (L * alg.U i) x q -
      alg.toCoefficients.gamma C i * (H * (L * alg.U i)) x q) ∈
        (Fintype.linearCombination K (fun i : G ↦ alg.V i)).ker := by
  classical
  change ∑ i : G, (alg.toCoefficients.gamma D i * (L * alg.U i) x q -
    alg.toCoefficients.gamma C i * (H * (L * alg.U i)) x q) • alg.V i = 0
  have hrow : (L x) ᵥ* D = ((H * L) x) ᵥ* C := by
    change (L * D) x = ((H * L) * C) x
    simpa only [Matrix.mul_assoc] using congrArg (fun M : Matrix N S K ↦ M x) hLD
  have hDproj := alg.supported_test_projection_formula G D hD (L x) (Pi.single q 1)
  have hCproj := alg.supported_test_projection_formula G C hC ((H * L) x) (Pi.single q 1)
  have hs :
      (∑ i : G, (alg.toCoefficients.gamma D i * (L * alg.U i) x q) • alg.V i) =
        ∑ i : G, (alg.toCoefficients.gamma C i * (H * (L * alg.U i)) x q) • alg.V i := by
    have he := hDproj.symm.trans ((congrArg (vecMulVec (Pi.single q 1)) hrow).trans hCproj)
    simpa only [single_dotProduct, one_mul, ← Matrix.mul_apply_eq_vecMul,
      Matrix.mul_assoc] using he
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib, hs, sub_self]

/-- При независимости вторых коэффициентов операторные отношения
обращаются в нуль покоординатно. -/
theorem operator_relation_zero_of_independent_second
    (alg : ExactAlgorithm K P Q S I) (G : Set I)
    (C D : Matrix P S K)
    (hC : C ∈ alg.toCoefficients.supportedTests G)
    (hD : D ∈ alg.toCoefficients.supportedTests G)
    (L : Matrix N P K) (H : Matrix N N K)
    (hLD : L * D = H * (L * C))
    (hV : LinearIndependent K (fun i : G ↦ alg.V i)) :
    ∀ i : G, alg.toCoefficients.gamma D i • (L * alg.U i) -
      alg.toCoefficients.gamma C i • (H * (L * alg.U i)) = 0 := by
  classical
  have hk := LinearMap.ker_eq_bot.mpr hV.fintypeLinearCombination_injective
  intro i
  ext x q
  have hm := alg.supported_slice_operator_relation_mem_kernel G C D hC hD L H hLD x q
  rw [hk] at hm
  exact congrFun ((Submodule.mem_bot K).mp hm) i

/-- Два поддержанных теста с общей операторной связью и одним отношением
соседей дают единый матричный множитель для всех координат. Ни общность,
ни регулярность, ни специальные физические размеры здесь не нужны. -/
theorem supported_slice_operator_relation
    (alg : ExactAlgorithm K P Q S I) (G : Set I)
    (C D : Matrix P S K)
    (hC : C ∈ alg.toCoefficients.supportedTests G)
    (hD : D ∈ alg.toCoefficients.supportedTests G)
    (L : Matrix N P K) (H : Matrix N N K)
    (hLD : L * D = H * (L * C))
    (hd : finrank K (Submodule.span K (alg.V '' G)) + 1 = G.ncard) :
    ∃ w : G → K, w ≠ 0 ∧
      (Fintype.linearCombination K (fun i : G ↦ alg.V i)).ker = Submodule.span K {w} ∧
      ∃ A : Matrix N Q K, ∀ i : G,
        alg.toCoefficients.gamma D i • (L * alg.U i) -
          alg.toCoefficients.gamma C i • (H * (L * alg.U i)) = w i • A := by
  classical
  have hV : Set.range (fun i : G ↦ alg.V i) = alg.V '' G := by ext V; simp
  obtain ⟨w, hw0, hw⟩ := exists_relation_generator_of_corank_one
    (fun i : G ↦ alg.V i) (by rw [hV, Set.fintypeCard_eq_ncard]; exact hd)
  obtain ⟨a, ha⟩ := relation_vectors_factor (fun i : G ↦ alg.V i) w hw
    (fun i : G ↦ fun xq : N × Q ↦
      alg.toCoefficients.gamma D i * (L * alg.U i) xq.1 xq.2 -
        alg.toCoefficients.gamma C i * (H * (L * alg.U i)) xq.1 xq.2)
    (fun xq ↦ alg.supported_slice_operator_relation_mem_kernel G C D hC hD L H hLD
      xq.1 xq.2)
  refine ⟨w, hw0, hw, (fun x q ↦ a (x, q)), ?_⟩
  intro i
  ext x q
  exact congrFun (ha i) (x, q)

/-- При полном носителе первого теста общий операторный множитель
нормируется покоординатно. Ранги и размер матрицы H произвольны. -/
theorem supported_slice_resolvent_relation [DecidableEq N]
    (alg : ExactAlgorithm K P Q S I) (G : Set I)
    (C D : Matrix P S K)
    (hC : C ∈ alg.toCoefficients.supportedTests G)
    (hD : D ∈ alg.toCoefficients.supportedTests G)
    (L : Matrix N P K) (H : Matrix N N K)
    (hLD : L * D = H * (L * C))
    (hd : finrank K (Submodule.span K (alg.V '' G)) + 1 = G.ncard)
    (hc : ∀ i : G, alg.toCoefficients.gamma C i ≠ 0) :
    ∃ w : G → K, w ≠ 0 ∧
      (Fintype.linearCombination K (fun i : G ↦ alg.V i)).ker = Submodule.span K {w} ∧
      ∃ A : Matrix N Q K, ∀ i : G,
        ((alg.toCoefficients.gamma D i / alg.toCoefficients.gamma C i) •
          (1 : Matrix N N K) - H) * (L * alg.U i) =
            (w i / alg.toCoefficients.gamma C i) • A := by
  obtain ⟨w, hw0, hw, A, ha⟩ := alg.supported_slice_operator_relation G C D hC hD L H hLD hd
  refine ⟨w, hw0, hw, A, ?_⟩
  intro i
  have hh := congrArg
    (fun X : Matrix N Q K ↦ (alg.toCoefficients.gamma C i)⁻¹ • X) (ha i)
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ (hc i), one_smul] at hh
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  simpa only [div_eq_mul_inv, mul_comm] using hh

end ExactAlgorithm
end MMRank
