module

public import MMRank.SupportedTestSpace
public import MMRank.CoordinateDuality
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-! # Перекрёстные отношения и нижние бюджеты нулевых типов -/

namespace MMRank
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K] [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Циклическая точность на простом входе даёт полную проекционную
формулу; аннулирование теста — её частный случай. -/
theorem ExactAlgorithm.test_projection_formula
    (alg : ExactAlgorithm K P Q S I) (C : Matrix P S K) (x : P → K) (y : Q → K) :
    vecMulVec y (x ᵥ* C) =
      ∑ i, (alg.toCoefficients.gamma C i * (y ⬝ᵥ (x ᵥ* alg.U i))) • alg.V i := by
  have hh := alg.rotate.rotate.exact_formula C (vecMulVec y x)
  change vecMulVec y x * C =
    ∑ i, (alg.toCoefficients.gamma C i * trace (alg.U i * vecMulVec y x)) • alg.V i at hh
  rw [vecMulVec_mul] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_mul_comm, vecMulVec_mul, trace_vecMulVec]

/-- Поддержанный тест ограничивает полную проекционную формулу на G. -/
theorem ExactAlgorithm.supported_test_projection_formula
    (alg : ExactAlgorithm K P Q S I) (G : Set I) (C : Matrix P S K)
    (hC : C ∈ alg.toCoefficients.supportedTests G) (x : P → K) (y : Q → K) :
    vecMulVec y (x ᵥ* C) =
      ∑ i : G, (alg.toCoefficients.gamma C i * (y ⬝ᵥ (x ᵥ* alg.U i))) • alg.V i := by
  rw [alg.test_projection_formula]
  exact Finset.sum_congr_set G _ _ (fun _ _ ↦ rfl) (fun i hi ↦ by
    rw [(Coefficients.mem_supportedTests _ _ _).mp hC i hi, zero_mul, zero_smul])

omit [Fintype Q] [Fintype S] [Fintype I] in
/-- Проекция полной фиксированной колонки даёт всё пространство строк. -/
theorem row_projection_span_eq_top (U : I → Matrix P Q K) (G : Set I)
    (p x : P → K) (hx : x ⬝ᵥ p = 1)
    (hU : fixedColumnSpace p ≤ Submodule.span K (U '' G)) :
    Submodule.span K ((fun i ↦ x ᵥ* U i) '' G) = ⊤ := by
  let L : Matrix P Q K →ₗ[K] (Q → K) := Matrix.vecMulBilin K K x
  have he : (Submodule.span K (U '' G)).map L =
      Submodule.span K ((fun i ↦ x ᵥ* U i) '' G) := by
    rw [Submodule.map_span, Set.image_image]
    rfl
  apply eq_top_iff.mpr
  intro y _
  rw [← he]
  refine ⟨vecMulVec p y, hU ⟨y, rfl⟩, ?_⟩
  change x ᵥ* vecMulVec p y = y
  rw [vecMul_vecMulVec, hx, one_smul]

end MMRank
