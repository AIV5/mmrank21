import MMRank.PhysicalConductorBounds
import MMRank.ConductorOrthogonality
import MMRank.SimpleHyperplaneNormalization
import MMRank.GenericHyperplane
import MMRank.InfiniteExtension

/-! # A lower bound for matrix multiplication of format ⟨2,2,n⟩

For a two-dimensional space M containing 1, the initial conductor bound
implies 2 dim N ≤ dim(N:M) + dim(MN). Orthogonality and the physical length
bound then give 7n ≤ 2ℓ over every field, including n=0.
This argument does not depend on the lower bound for 3 × 3 multiplication.
-/

namespace MMRank.ExactAlgorithm

open Module

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- The bound for a normalized algorithm over any field.
The hypotheses are a nonzero hyperplane form and the unit in its coefficient space. -/
theorem length_bound_two_by_two_of_normalized
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι)
    (hp : Fintype.card P = 2) (hq : Fintype.card Q = 2)
    (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η)) :
    7 * Fintype.card S ≤ 2 * Fintype.card ι := by
  let M := alg.toCoefficients.alphaOn (coordinateHyperplane η)
  let N := alg.toCoefficients.gamma.range
  let B := alg.toCoefficients.betaInto (coordinateHyperplane η)
  have hF : finrank K (coordinateHyperplane η) = 1 := by
    have := finrank_coordinateHyperplane_add_one η hη
    omega
  have hM : finrank K M = 2 := by
    simp [M, alg.finrank_alphaOn, hp, hq, hF]
  have hN : finrank K N = 2 * Fintype.card S := by
    simp [N, alg.finrank_range_gamma, hp, Nat.mul_comm]
  have hB : finrank K B = Fintype.card S := by
    simp [B, alg.finrank_betaInto, hF]
  have hprod := finrank_product_add_le_of_orthogonal M B N
    (alg.restricted_product_le_orthogonal (coordinateHyperplane η))
  have hg := finrank_conductor_growth_bound M N h1
  have hle := Submodule.finrank_mono (le_mul_of_one_mem M N h1)
  have hde := (finrank_conductor_saturated_pair M N h1).1
  have hphys := alg.saturated_physical_length_bound η hη
  change Fintype.card P * Fintype.card S + (Fintype.card Q - 1) *
    finrank K (M * conductor N M) ≤ Fintype.card ι at hphys
  rw [hM, hN] at hg
  rw [hN] at hle
  rw [hB] at hprod
  rw [hp, hq] at hphys
  omega

/-- Every exact algorithm of format ⟨2,2,n⟩ satisfies 7n ≤ 2ℓ.
The field is arbitrary; zero terms and an empty S are allowed.
No minimality assumption is imposed on the algorithm. -/
theorem length_bound_two_by_two (alg : ExactAlgorithm K P Q S ι)
    (hp : Fintype.card P = 2) (hq : Fintype.card Q = 2) :
    7 * Fintype.card S ≤ 2 * Fintype.card ι := by
  by_cases hs : Fintype.card S = 0
  · simp [hs]
  let : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty S := Fintype.card_pos_iff.mp (by omega)
  let : Infinite (RatFunc K) := ratFunc_infinite K
  obtain ⟨a, ha⟩ := alg.exists_nonzero_length_ratFunc
    (by rw [hp, hq]; decide) (Fintype.card ι) le_rfl
  obtain ⟨η, hη, u, h1⟩ := a.toCoefficients.exists_rescale_one_mem_hyperplane
    (fun i ↦ (ha i).1)
  have h := (a.rescale u).length_bound_two_by_two_of_normalized hp hq η hη h1
  simpa only [Fintype.card_fin] using h

/-- The integer bound ℓ ≥ ⌈7n/2⌉, including n=0.
In ℕ, the ceiling is written as (7*n+1)/2. -/
theorem length_22n_ge_ceil {n : ℕ}
    (alg : ExactAlgorithm K (Fin 2) (Fin 2) (Fin n) ι) :
    (7 * n + 1) / 2 ≤ Fintype.card ι := by
  have h := alg.length_bound_two_by_two (by decide) (by decide)
  simp only [Fintype.card_fin] at h
  omega

end MMRank.ExactAlgorithm
