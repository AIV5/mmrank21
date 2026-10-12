module

public import MMRank.PhysicalConductor

@[expose] public section

/-! # Линейное отображение, согласованное с одной линейной формой -/

namespace MMRank
open Matrix Module
variable {K U W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]

/-- Симметрия относительно ненулевой формы вынуждает общий одномерный образ.
Конечномерность пространств не требуется. -/
theorem exists_factor_of_scalar_reciprocity (l : U →ₗ[K] K) (hl : l ≠ 0)
    (f : U →ₗ[K] W) (h : ∀ u v, l v • f u = l u • f v) :
    ∃ w : W, ∀ u, f u = l u • w := by
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra! hz
    exact hl (LinearMap.ext hz)
  refine ⟨(l v)⁻¹ • f v, fun u ↦ ?_⟩
  have hh := congrArg (fun x : W ↦ (l v)⁻¹ • x) (h u v)
  simpa [smul_smul, hv, mul_comm] using hh

variable {P S : Type*} [Fintype P]

/-- Матричная форма той же леммы для правого действия на строках. -/
theorem exists_outer_of_dot_reciprocity (p : P → K) (hp : p ≠ 0)
    (C : Matrix P S K)
    (h : ∀ u v, (v ⬝ᵥ p) • (u ᵥ* C) = (u ⬝ᵥ p) • (v ᵥ* C)) :
    ∃ s : S → K, C = vecMulVec p s := by
  classical
  let l : (P → K) →ₗ[K] K := dotProductBilin K K p
  have hl : l ≠ 0 := by
    intro hz
    apply hp
    ext j
    have hh := DFunLike.congr_fun hz (Pi.single j 1)
    simpa [l, dotProduct, Pi.single_apply] using hh
  obtain ⟨s, hs⟩ := exists_factor_of_scalar_reciprocity l hl C.vecMulLinear
    (by
      intro u v
      change (p ⬝ᵥ v) • (u ᵥ* C) = (p ⬝ᵥ u) • (v ᵥ* C)
      simpa only [dotProduct_comm] using h u v)
  refine ⟨s, ?_⟩
  ext j k
  have hh := congrFun (hs (Pi.single j 1)) k
  simpa [l, dotProduct, Pi.single_apply, vecMulVec] using hh

end MMRank
