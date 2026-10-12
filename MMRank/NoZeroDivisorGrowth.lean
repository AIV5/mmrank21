module

public import MMRank.ConnectivityCost
public import MMRank.CoordinateProductGrowth

@[expose] public section

/-! # Цена насыщенного роста при отсутствии делителей нуля

На каждом активном устойчивом блоке ограничение множителей инъективно.
Поэтому цена связности равна полной проективной размерности множителей.
-/

namespace MMRank

open Module

variable {K ι : Type*} [Field K]

variable [Finite ι]

/-- Ненулевой насыщенный кондуктор растёт хотя бы на dim M − 1. -/
theorem saturated_growth_of_noZeroDivisors (M N : Submodule K (ι → K))
    (h1 : (1 : ι → K) ∈ M) (hD : conductor N M ≠ ⊥)
    (hnz : ∀ a ∈ M, ∀ b ∈ N, a * b = 0 → a = 0 ∨ b = 0) :
    finrank K M + finrank K (conductor N M) ≤ finrank K (M * conductor N M) + 1 := by
  obtain ⟨w, hw, hw0⟩ := (conductor N M).ne_bot_iff.mp hD
  have hM : M ≠ ⊥ := by
    intro hz
    have hunit : (1 : ι → K) = 0 := by simpa only [hz, Submodule.mem_bot] using h1
    exact hw0 (by simpa only [one_mul, zero_mul] using congrArg (· * w) hunit)
  exact coordinate_product_growth_of_noZeroDivisors M (conductor N M) hM hD
    (fun a ha b hb ↦ hnz a ha b (conductor_le_of_one_mem N M h1 hb))

end MMRank
