module

public import MMRank.ConductorFactorRanks
public import MMRank.JointSymmetrizerFactorShort
public import MMRank.SeparableSecondConductorProduct
public import MMRank.NormalizedHyperplane

@[expose] public section

/-! # Исключение большого насыщения при dim Z=2

Над произвольным полем профиль e≥5,z=2 требует длины≥21.
Сильный резервный пакет с точными ограниченными рангами Vᵢ даёт≥27.
-/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]
  [Nonempty P] [Nonempty Q] [Nonempty S]

/-- Физические факторы в произвольных трёхэлементных индексах P,S. -/
theorem secondConductor_exists_equiv_factors_of_card
    (alg : ExactAlgorithm K P Q S ι)
    (hp : Fintype.card P = 3) (hs : Fintype.card S = 3)
    (η : Q → K) (hη : η ≠ 0) (hF : finrank K (coordinateHyperplane η) < 3)
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ b ∈ alg.toCoefficients.betaInto (coordinateHyperplane η),
      a * b = 0 → a = 0 ∨ b = 0)
    (hE : 5 ≤ finrank K (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))))
    (hZ : conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) ≠ ⊥)
    (hd : finrank K (conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) = finrank K (coordinateHyperplane η)) :
    ∃ L : (P → K) ≃ₗ[K] (S → K),
      ∃ e : conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
        (alg.toCoefficients.alphaOn (coordinateHyperplane η)) ≃ₗ[K] coordinateHyperplane η,
        ∀ z u s, alg.hyperplaneSecondConductorFamily η z u s =
          (s ⬝ᵥ L u) • (e z).val := by
  classical
  let : Nontrivial (conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
    (alg.toCoefficients.alphaOn (coordinateHyperplane η))) := Submodule.nontrivial_iff_ne_bot.mpr hZ
  obtain ⟨L, e, he⟩ := exists_abstract_equiv_factors_of_five_jointSymmetrizers
    (alg.hyperplaneSecondConductorFamily η) (by simpa using hp) (by simpa using hs)
    (coordinateHyperplane η) hF hd (alg.hyperplaneSecondConductorFamily_mem η)
    (hE.trans (alg.saturated_finrank_le_jointSymmetrizer η hη))
    (alg.hyperplaneSecondConductorFamily_nz η hη h1 hnz)
  refine ⟨L.trans (dotProductEquiv K S).symm, e, ?_⟩
  intro z u s
  have hh := DFunLike.congr_fun ((dotProductEquiv K S).apply_symm_apply (L u)) s
  change ((dotProductEquiv K S).symm (L u) ⬝ᵥ s) = L u s at hh
  rw [he, ← hh, dotProduct_comm]
  rfl

/-- Без рангового общего положения: e≥5,z=2 в нормированном333
требуют длину≥21 прямой инъективностью γ·Z. -/
theorem length_ge_twenty_one_of_large_saturation_second_two
    (alg : ExactAlgorithm K P Q S ι) (h : NormalizedHyperplaneCore alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hE : 5 ≤ finrank K (alg.toCoefficients.alphaOn h.F *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F)))
    (hZ : finrank K (conductor (alg.toCoefficients.betaInto h.F)
      (alg.toCoefficients.alphaOn h.F)) = 2) :
    21 ≤ Fintype.card ι := by
  have hF : finrank K h.F = 2 := by have := h.codim_one; omega
  obtain ⟨η, hη, heF⟩ := exists_coordinateHyperplane_of_finrank_add_one h.F h.codim_one
  have hone := h.one_mem
  have hnz := h.restricted_nz
  rw [heF] at hF hE hZ hone hnz
  obtain ⟨L, e, hf⟩ := alg.secondConductor_exists_equiv_factors_of_card hp hs η hη
    (by omega) hone hnz hE (by intro hz; rw [hz, finrank_bot] at hZ; omega) (by omega)
  have hh := alg.length_bound_of_separable_secondConductor η hone L.toLinearMap L.surjective
    e.toLinearMap e.injective (alg.secondConductorMatrix_eq_outer_of_factor η L.toLinearMap e.toLinearMap hf)
  rw [hp, hs, hZ, alg.finrank_alphaOn, hq, hF] at hh
  omega

end MMRank.ExactAlgorithm
