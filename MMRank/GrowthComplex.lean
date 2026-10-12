import MMRank.ConductorGrowth
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Tactic.FinCases

/-!
# Начало комплекса роста и точная размерность кондуктора

Умножение представителей индуцирует L × G₁ → G₂, где L=M/R1,
G₁=MN/N, G₂=M(MN)/MN при 1 ∈ M. Построено δ₁ со значениями в Hom(Λ²L,G₂).
В правой записи δ₀δ₁=0, в mathlib — δ₁.comp δ₀=0. Точность в середине
и сюръективность δ₁ не предполагаются: H¹ сохраняется в размерностной формуле.
-/

namespace MMRank

open Module

section Ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Вторая ступень роста; при 1 ∈ M это M²N/MN. -/
abbrev SecondGrowth (M N : Submodule R A) := FirstGrowth M (M * N)

private def nextGrowthAction (M N : Submodule R A) :
    M →ₗ[R] FirstGrowth M N →ₗ[R] SecondGrowth M N where
  toFun m := (N.comap (M * N).subtype).liftQ (growthAction M (M * N) m) (by
    intro n hn
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.mul_mem_mul m.property hn)
  map_add' m m' := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H n => exact congrArg (fun f => f n) ((growthAction M (M * N)).map_add m m')
  map_smul' r m := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H n => exact congrArg (fun f => f n) ((growthAction M (M * N)).map_smul r m)

/-- Умножение L × G₁ → G₂, корректное по обоим факторпространствам. -/
def secondGrowthAction (M N : Submodule R A) (hM : (1 : A) ∈ M) :
    MultiplierDirections M hM →ₗ[R] FirstGrowth M N →ₗ[R] SecondGrowth M N :=
  (Submodule.span R {(⟨1, hM⟩ : M)}).liftQ (nextGrowthAction M N) (by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H n =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change (1 : A) * n.val ∈ M * N
      simpa only [one_mul] using n.property)

@[simp] theorem secondGrowthAction_apply_mk (M N : Submodule R A)
    (hM : (1 : A) ∈ M) (m : M) (n : M * N) :
    secondGrowthAction M N hM (Submodule.Quotient.mk m) (Submodule.Quotient.mk n) =
      Submodule.Quotient.mk (submoduleMul M (M * N) m n) := rfl

end Ring

section Differential

variable {R L V W : Type*} [CommRing R]
  [AddCommGroup L] [Module R L] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- Знакопеременная производная: (u∧v)(φδ)=(vφ)u−(uφ)v для действия μ. -/
def alternatingDifferential (μ : L →ₗ[R] V →ₗ[R] W) :
    (L →ₗ[R] V) →ₗ[R] AlternatingMap R L W (Fin 2) where
  toFun f :=
    { toFun := fun v => μ (v 0) (f (v 1)) - μ (v 1) (f (v 0))
      map_update_add' := by
        intro _ v i x y
        fin_cases i <;> simp [map_add, sub_add_sub_comm]
      map_update_smul' := by
        intro _ v i r x
        fin_cases i <;> simp [smul_sub]
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        fin_cases i <;> fin_cases j <;> simp_all }
  map_add' f g := by
    ext v
    simp [map_add, sub_add_sub_comm]
  map_smul' r f := by
    ext v
    simp [smul_sub]

end Differential

section Ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- δ₁ со значениями именно в Hom(Λ²L,G₂), через универсальное свойство Λ²L. -/
noncomputable def secondGrowthMap (M N : Submodule R A) (hM : (1 : A) ∈ M) :
    (MultiplierDirections M hM →ₗ[R] FirstGrowth M N) →ₗ[R]
      (⋀[R]^2 (MultiplierDirections M hM)) →ₗ[R] SecondGrowth M N :=
  exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
    (alternatingDifferential (secondGrowthAction M N hM))

@[simp] theorem secondGrowthMap_apply_ιMulti (M N : Submodule R A)
    (hM : (1 : A) ∈ M) (f : MultiplierDirections M hM →ₗ[R] FirstGrowth M N)
    (v : Fin 2 → MultiplierDirections M hM) :
    secondGrowthMap M N hM f (exteriorPower.ιMulti R 2 v) =
      secondGrowthAction M N hM (v 0) (f (v 1)) -
        secondGrowthAction M N hM (v 1) (f (v 0)) := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

end Ring

section Cohomology

variable {K X Y Z : Type*} [DivisionRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

end Cohomology

section Field

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

end Field

end MMRank
