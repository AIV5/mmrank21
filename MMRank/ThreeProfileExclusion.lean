import MMRank.SecondConductorProductRank
import MMRank.PhysicalAtomDiagonal
import MMRank.ZeroGrowthPhysicalAtoms

/-! # Профиль (3,3) исключён одной оценкой 18+3

Три атома одной ориентации дают согласованные простые тесты. Малый первый
кондуктор и общая оценка произведения второго кондуктора требуют длину>=21.
Точное равенство dim Z=2 и алгебраическая замкнутость для этого перехода не нужны.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K] [Infinite K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Полный запрет нулевого роста с d=3 при333 и длине≤20. -/
theorem zero_growth_three_profile_impossible
    (alg : ExactAlgorithm K P Q S I) (h : NormalizedHyperplaneCore alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20)
    (he : alg.toCoefficients.alphaOn h.F *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F) =
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F))
    (hd : finrank K (conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F)) = 3) :
    False := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty S := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a, ha⟩ := alg.exists_physical_atoms_of_zero_growth h hp hq hs hl he 3 hd.ge
  obtain ⟨b, c, hb, hc⟩ := PhysicalAtom.exists_three_atom_bases a hp hq hs hl h.nonzero_terms ha
  obtain ⟨η, hη, hF, _⟩ := h.generic_column
  have h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η) :=
    by simpa only [← hF] using h.one_mem
  have hnz : ∀ u ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ v ∈ alg.toCoefficients.betaInto (coordinateHyperplane η), u * v = 0 → u = 0 ∨ v = 0 :=
    by simpa only [← hF] using h.restricted_nz
  have ht j : alg.toCoefficients.gamma (rowLinearEquiv.symm ((b.coord j).smulRight (c j))) ∈
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)) := by
    rw [← PhysicalAtom.test_eq_basis_simple a b c hb hc, rowLinearEquiv.symm_apply_apply]
    exact (a j).test_mem_conductor η hη h1
  have hh := alg.length_ge_twenty_one_of_small_diagonal_conductor hp hq hs η hη h1 hnz b c ht
    (by rw [← hF, hd])
  omega

end MMRank.ExactAlgorithm
