module

public import MMRank.ResidualTraceIdentity
public import Mathlib.LinearAlgebra.Projection
public import MMRank.PhysicalAtomUnion

@[expose] public section

/-! # Прямой переход от физических атомов к фактор-тождеству

Никакой нормальной формы атомных блоков
и дополнительной нормировки алгоритма не требуется.
-/
set_option backward.isDefEq.respectTransparency false
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I J : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Свёртка точного тензорного тождества по средним координатам:
Σ tr(W_i C) U_i X V_i = tr(X) C, во всех физических размерах. -/
theorem sandwich_trace_identity (alg : ExactAlgorithm K P Q S I)
    (C : Matrix P S K) (X : Matrix Q Q K) :
    ∑ i, trace (alg.W i * C) • (alg.U i * X * alg.V i) = trace X • C := by
  classical
  let F : Matrix Q Q K →ₗ[K] Matrix P S K :=
    ∑ i, trace (alg.W i * C) • matrixSandwich (alg.U i) (alg.V i)
  have he : F = (traceLinearMap Q K K).smulRight C := by
    apply Matrix.ext_linearMap
    intro q r
    apply LinearMap.ext_ring
    ext p s
    have hh := congrArg (fun A : Matrix Q S K ↦ A r s)
      (alg.rotate.rotate.exact_formula C (single q p (1 : K)))
    change (single q p (1 : K) * C) r s =
      (∑ i, (trace (alg.W i * C) * trace (alg.U i * single q p (1 : K))) • alg.V i) r s at hh
    simpa [F, Matrix.mul_apply, single_apply, Matrix.sum_apply, Finset.sum_mul,
      smul_eq_mul, trace_mul_single, Matrix.trace, ite_and, mul_assoc, eq_comm] using hh.symm
  simpa [F] using DFunLike.congr_fun he X

namespace PhysicalAtom
variable {alg : ExactAlgorithm K P Q S I}

/-- Любая средняя матрица между атомными U_i,V_i даёт кратный тест атома. -/
theorem sandwich_mem_test_line (a : alg.PhysicalAtom) {i : I} (hi : i ∈ a.support)
    (X : Matrix Q Q K) : alg.U i * X * alg.V i ∈ Submodule.span K {a.test} := by
  obtain ⟨u, hu⟩ := a.U_mem hi
  change vecMulVec a.first u = alg.U i at hu
  have hl : (u ᵥ* X) ᵥ* alg.V i ∈ Submodule.span K {a.last} :=
    (mem_matricesInto _ _).mp (a.V_mem hi) ⟨u ᵥ* X, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hl
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  rw [← hu, vecMulVec_mul, vecMulVec_mul, ← hc, vecMulVec_smul]
  rfl

/-- Пространство удаляемых физических тестов. -/
def testSpan (a : J → alg.PhysicalAtom) : Submodule K (Matrix P S K) :=
  Submodule.span K (Set.range fun j ↦ (a j).test)

end PhysicalAtom

end MMRank.ExactAlgorithm
