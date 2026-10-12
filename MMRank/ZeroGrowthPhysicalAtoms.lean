import MMRank.PhysicalAtomTransport
import MMRank.InvariantPhysicalAtoms

/-! # Семейства физических атомов исходного алгоритма из нулевого роста -/
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Нулевой рост даёт любое число физических атомов, не превосходящее dimD.
Утверждение действует над любым полем при указанной нормировке. -/
theorem exists_physical_atoms_of_zero_growth
    (alg : ExactAlgorithm K P Q S I) (h : NormalizedHyperplaneCore alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20)
    (he : alg.toCoefficients.alphaOn h.F *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F) =
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F))
    (n : ℕ) (hn : n ≤ finrank K (conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn h.F))) :
    ∃ a : Fin n → PhysicalAtom alg, Function.Injective (fun j => (a j).support) := by
  obtain ⟨η, hη, hF, hcol⟩ := h.generic_column
  obtain ⟨a, ha, _⟩ := alg.exists_physical_atoms_of_invariant hp hq hs hl η hη hcol
    (by simpa only [← hF] using h.one_mem)
    (conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F))
    (conductor_le_of_one_mem _ _ h.one_mem)
    (by simpa only [← hF] using he) n hn
  exact ⟨a, ha⟩

end MMRank.ExactAlgorithm
