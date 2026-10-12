import MMRank.RestrictedCoefficients
import MMRank.ConductorAlternatingBound

/-! # Прямое применение оценки двух кондукторов к точному алгоритму

Только ограниченные размерности,
ортогональность и общая знакопеременная оценка; без комплекса роста.
-/
namespace MMRank.ExactAlgorithm
open Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Нижняя оценка суммы размерностей двух кондукторов при pc=3. -/
theorem restricted_two_conductor_dimension_sum_bound [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (c : ℕ) (hc : c ≤ Fintype.card Q) (hF : finrank K F = Fintype.card Q - c)
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn F) (hpc : Fintype.card P * c = 3) :
    3 * (Fintype.card P * Fintype.card S) + Fintype.card S * (Fintype.card Q - c) ≤
      finrank K (conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F)) +
      finrank K (conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F)) +
      2 * (Fintype.card ι - Fintype.card S * (Fintype.card Q - c)) := by
  obtain ⟨hM, hB, hN⟩ := alg.restricted_dimensions F c hc hF
  have horth := (le_coordinateOrthogonal_mul_iff (alg.toCoefficients.alphaOn F)
    (alg.toCoefficients.betaInto F) alg.toCoefficients.gamma.range).mpr
      (alg.restricted_product_le_orthogonal F)
  have h := two_conductor_dimension_sum_bound _ _ _ h1 (hM.trans hpc) horth
  rwa [hN, hB] at h

end MMRank.ExactAlgorithm
