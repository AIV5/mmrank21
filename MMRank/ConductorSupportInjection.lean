module

public import MMRank.PhysicalConductorBounds
public import MMRank.FullBetaNoZeroDivisors
public import MMRank.RestrictedSupport
public import MMRank.CoordinateDuality

@[expose] public section

/-! # Носитель кондуктора и инъективное физическое семейство

Большой носитель D не позволяет ненулевому элементу A_F зануляться на нём.
Над бесконечным полем один элемент D реализует весь его носитель.
-/

namespace MMRank

open Module Matrix

variable {K ι : Type*} [Field K]

/-- Над бесконечным полем конечный координатный носитель пространства
реализуется одним словом, даже если он не полон. -/
theorem exists_mem_support_eq [Infinite K] [Finite ι] (N : Submodule K (ι → K)) :
    ∃ w ∈ N, ∀ i, w i ≠ 0 ↔ ∃ v ∈ N, v i ≠ 0 := by
  let s : Set ι := {i | ∃ v ∈ N, v i ≠ 0}
  obtain ⟨w, hw, hh⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists N
    (fun i : s ↦ LinearMap.proj i.val) (fun i ↦ i.property)
  refine ⟨w, hw, fun i ↦ ⟨fun hi ↦ ⟨w, hw, hi⟩, fun hi ↦ ?_⟩⟩
  exact hh ⟨i, hi⟩

namespace ExactAlgorithm

variable {P Q S : Type*} [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

end ExactAlgorithm
end MMRank
