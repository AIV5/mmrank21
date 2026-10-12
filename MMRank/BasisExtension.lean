import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Базис с предписанным ненулевым вектором -/
namespace MMRank
open Module

/-- Любой ненулевой вектор можно включить в базис с заданным типом индексов.
Размерности и конечность индексов не нужны. -/
theorem exists_basis_containing_nonzero {K E J : Type*} [DivisionRing K]
    [AddCommGroup E] [Module K E] (b₀ : Basis J K E) (x : E) (hx : x ≠ 0) :
    ∃ b : Basis J K E, ∃ j, b j = x := by
  classical
  have hs : LinearIndepOn K id {x} := LinearIndepOn.singleton hx
  let b := Basis.extend hs
  let e := b.indexEquiv b₀
  let i : hs.extend (Set.subset_univ _) := ⟨x, hs.subset_extend _ (Set.mem_singleton x)⟩
  refine ⟨b.reindex e, e i, ?_⟩
  simp [b, i]

end MMRank
