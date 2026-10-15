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

/-- Ядро δ₀ — кондуктор, представленный как подмодуль N. -/
theorem ker_firstGrowthMap (M N : Submodule R A) (hM : (1 : A) ∈ M) :
    (firstGrowthMap M N hM).ker = (conductor N M).comap N.subtype := by
  ext n
  change firstGrowthMap M N hM n = 0 ↔ n.val ∈ conductor N M
  rw [mem_conductor]
  constructor
  · intro hn m hm
    have h := congrArg (fun f : MultiplierDirections M hM →ₗ[R] FirstGrowth M N ↦
      f (Submodule.Quotient.mk ⟨m, hm⟩)) hn
    have ht : submoduleMul M N ⟨m, hm⟩ n ∈ N.comap (M * N).subtype :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    exact ht
  · intro hn
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H m =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact hn m.val m.property

end Ring

section Field

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]

/-- dim G₁ = dim MN − dim N при наличии единицы в M. -/
theorem finrank_firstGrowth (M N : Submodule K A) (hM : (1 : A) ∈ M) :
    finrank K (FirstGrowth M N) = finrank K (M * N) - finrank K N := by
  have he : finrank K (N.comap (M * N).subtype) = finrank K N := by
    rw [← Submodule.finrank_map_subtype_eq (M * N), Submodule.map_comap_subtype,
      inf_eq_right.mpr (le_mul_of_one_mem M N hM)]
  have h := (N.comap (M * N).subtype).finrank_quotient_add_finrank
  rw [he] at h
  exact Nat.eq_sub_of_add_eq h

/-- dim L = dim M − 1, с усечённым вычитанием для нулевой алгебры. -/
theorem finrank_multiplierDirections
    (M : Submodule K A) (hM : (1 : A) ∈ M) :
    finrank K (MultiplierDirections M hM) = finrank K M - 1 := by
  nontriviality A
  have h := (Submodule.span K {(⟨1, hM⟩ : M)}).finrank_quotient_add_finrank
  have hn : (⟨1, hM⟩ : M) ≠ 0 := fun h ↦ one_ne_zero (congrArg Subtype.val h)
  rw [finrank_span_singleton hn] at h
  exact Nat.eq_sub_of_add_eq h

omit [FiniteDimensional K A] in
/-- Размерность ядра δ₀ равна размерности кондуктора в исходной алгебре. -/
theorem finrank_ker_firstGrowthMap (M N : Submodule K A) (hM : (1 : A) ∈ M) :
    finrank K (firstGrowthMap M N hM).ker = finrank K (conductor N M) := by
  rw [ker_firstGrowthMap, ← Submodule.finrank_map_subtype_eq N,
    Submodule.map_comap_subtype, inf_eq_right.mpr (conductor_le_of_one_mem N M hM)]

/-- Начальная оценка: dim N ≤ dim D + (dim M−1)(dim MN−dim N).
Поправки от δ₁ и когомологий здесь не используются. -/
theorem finrank_conductor_growth_bound
    (M N : Submodule K A) (hM : (1 : A) ∈ M) :
    finrank K N ≤ finrank K (conductor N M) +
      (finrank K M - 1) * (finrank K (M * N) - finrank K N) := by
  nontriviality A
  have h := (firstGrowthMap M N hM).finrank_range_add_finrank_ker
  have hr := (firstGrowthMap M N hM).range.finrank_le
  rw [Module.finrank_linearMap, finrank_multiplierDirections M hM,
    finrank_firstGrowth M N hM] at hr
  rw [finrank_ker_firstGrowthMap M N hM] at h
  omega

/-- Размерностные ограничения насыщенной пары; положительность кондуктора не нужна. -/
theorem finrank_conductor_saturated_pair (M N : Submodule K A) (hM : (1 : A) ∈ M) :
    finrank K (conductor N M) ≤ finrank K (M * conductor N M) ∧
      finrank K (M * conductor N M) ≤ finrank K N :=
  ⟨Submodule.finrank_mono (le_mul_of_one_mem M _ hM),
    Submodule.finrank_mono (mul_conductor_le M N)⟩

end Field

end MMRank
