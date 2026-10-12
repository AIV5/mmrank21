import MMRank.Conductor
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Первый шаг роста и начальная оценка кондуктора

G₁ = MN/N, L = M/R1. Умножение задаёт δ₀ : N → Hom(L,G₁), ker δ₀ = (N:M).
Здесь ещё не строится δ₁ и не предполагается точность комплекса в середине.
-/

namespace MMRank

open Module

section Ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Фактор MN по N ∩ MN; при 1 ∈ M это первая ступень роста MN/N. -/
abbrev FirstGrowth (M N : Submodule R A) := (M * N) ⧸ N.comap (M * N).subtype

/-- Направления умножения по модулю скалярного направления единицы. -/
abbrev MultiplierDirections (M : Submodule R A) (hM : (1 : A) ∈ M) :=
  M ⧸ Submodule.span R {(⟨1, hM⟩ : M)}

/-- Умножение с явно ограниченным пространством значений MN. -/
def submoduleMul (M N : Submodule R A) : M →ₗ[R] N →ₗ[R] (M * N) where
  toFun m :=
    { toFun n := ⟨m.val * n.val, Submodule.mul_mem_mul m.property n.property⟩
      map_add' n n' := by apply Subtype.ext; exact mul_add _ _ _
      map_smul' r n := by apply Subtype.ext; exact Algebra.mul_smul_comm _ _ _ }
  map_add' m m' := by ext n; exact add_mul _ _ _
  map_smul' r m := by ext n; exact Algebra.smul_mul_assoc _ _ _

/-- Умножение представителей с последующим переходом к G₁. -/
def growthAction (M N : Submodule R A) : M →ₗ[R] N →ₗ[R] FirstGrowth M N :=
  (submoduleMul M N).compr₂ (N.comap (M * N).subtype).mkQ

/-- Скалярное направление единицы зануляется в G₁. -/
theorem oneSpan_le_ker_growthAction (M N : Submodule R A) (hM : (1 : A) ∈ M) :
    Submodule.span R {(⟨1, hM⟩ : M)} ≤ (growthAction M N).ker := by
  rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
  apply LinearMap.ext
  intro n
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (1 : A) * n.val ∈ N
  simpa only [one_mul] using n.property

/-- δ₀(n)(m mod R1) = mn mod N; корректность факторизации доказана, не постулирована. -/
def firstGrowthMap (M N : Submodule R A) (hM : (1 : A) ∈ M) :
    N →ₗ[R] MultiplierDirections M hM →ₗ[R] FirstGrowth M N :=
  ((Submodule.span R {(⟨1, hM⟩ : M)}).liftQ (growthAction M N)
    (oneSpan_le_ker_growthAction M N hM)).flip

@[simp] theorem firstGrowthMap_apply_mk (M N : Submodule R A) (hM : (1 : A) ∈ M)
    (n : N) (m : M) :
    firstGrowthMap M N hM n (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (submoduleMul M N m n) := rfl

end Ring

section Field

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]

/-- Размерностные ограничения насыщенной пары; положительность кондуктора не нужна. -/
theorem finrank_conductor_saturated_pair (M N : Submodule K A) (hM : (1 : A) ∈ M) :
    finrank K (conductor N M) ≤ finrank K (M * conductor N M) ∧
      finrank K (M * conductor N M) ≤ finrank K N :=
  ⟨Submodule.finrank_mono (le_mul_of_one_mem M _ hM),
    Submodule.finrank_mono (mul_conductor_le M N)⟩

end Field

end MMRank
