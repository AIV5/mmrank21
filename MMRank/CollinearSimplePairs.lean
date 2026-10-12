import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace MMRank
open Module

/-- Если простые пары лежат на одной прямой, их первые множители
коллинеарны после исключения нулевых вторых множителей. -/
theorem linearForms_collinear_of_smulRight_span_le_one
    {K X Y I : Type*} [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (a : I → X →ₗ[K] K) (b : I → Y)
    (hd : finrank K (Submodule.span K (Set.range (fun i ↦ (a i).smulRight (b i)))) ≤ 1)
    (i j : I) (hi : b i ≠ 0) (hj : b j ≠ 0) (x y : X) :
    a i x * a j y = a i y * a j x := by
  by_cases haj : a j = 0
  · simp [haj]
  let E := Submodule.span K (Set.range (fun i ↦ (a i).smulRight (b i)))
  have hpj : (a j).smulRight (b j) ≠ 0 := by
    intro hz
    rcases LinearMap.smulRight_apply_eq_zero_iff.mp hz with hz | hz
    · exact haj hz
    · exact hj hz
  have hm : (a j).smulRight (b j) ∈ E := Submodule.subset_span (Set.mem_range_self j)
  have hlo := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hm)
  rw [finrank_span_singleton hpj] at hlo
  have he := eq_span_singleton_of_mem_of_finrank_eq_one (Nat.le_antisymm hd hlo) hm hpj
  change E = Submodule.span K {(a j).smulRight (b j)} at he
  have hpi : (a i).smulRight (b i) ∈ E := Submodule.subset_span (Set.mem_range_self i)
  rw [he, Submodule.mem_span_singleton] at hpi
  obtain ⟨c, hc⟩ := hpi
  obtain ⟨φ, hφ, _⟩ := Submodule.exists_le_ker_of_notMem
    (show b i ∉ (⊥ : Submodule K Y) by simpa using hi)
  have hx := congrArg φ (DFunLike.congr_fun hc x)
  have hy := congrArg φ (DFunLike.congr_fun hc y)
  simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul] at hx hy
  apply mul_right_cancel₀ hφ
  calc
    (a i x * a j y) * φ (b i) = a j y * (a i x * φ (b i)) := by ring
    _ = a j y * (c * (a j x * φ (b j))) := by rw [← hx]
    _ = a j x * (c * (a j y * φ (b j))) := by ring
    _ = a j x * (a i y * φ (b i)) := by rw [hy]
    _ = (a i y * a j x) * φ (b i) := by ring

end MMRank
