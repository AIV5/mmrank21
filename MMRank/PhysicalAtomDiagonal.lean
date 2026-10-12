module

public import MMRank.PhysicalAtomFullClasses
public import MMRank.PhysicalAtomDirections

@[expose] public section

/-! # Атомные базисы и диагональный мост к нулевому правилу -/
namespace MMRank
open Matrix Module
variable {K P J : Type*} [Field K] [Fintype P] [Fintype J]

/-- Базис ковекторов задаёт двойственный базис строк без смены конвенции действия. -/
theorem exists_basis_coord_dotProduct (a : Basis J K (P → K)) :
    ∃ b : Basis J K (P → K), ∀ j u, b.coord j u = u ⬝ᵥ a j := by
  classical
  refine ⟨a.dualBasis.map (dotProductEquiv K P).symm, ?_⟩
  intro j u
  change a.dualBasis.repr (dotProductEquiv K P u) j = _
  rw [Basis.dualBasis_repr]
  rfl

namespace ExactAlgorithm.PhysicalAtom
variable {Q S I : Type*} [Fintype Q] [Fintype S] [Fintype I]
  {alg : ExactAlgorithm K P Q S I}

/-- Три различных атома333≤20 дают согласованные физические базисы.
Первый базис двойственен first; второй состоит из last. -/
theorem exists_three_atom_bases [Infinite K]
    (a : Fin 3 → PhysicalAtom alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (hn : alg.toCoefficients.NonzeroTerms)
    (hd : Function.Injective (fun j ↦ (a j).support)) :
    ∃ b : Basis (Fin 3) K (P → K), ∃ c : Basis (Fin 3) K (S → K),
      (∀ j u, b.coord j u = u ⬝ᵥ (a j).first) ∧ ∀ j, c j = (a j).last := by
  have hi := three_directions_linearIndependent a hp hq hs hl hn hd
  obtain ⟨f, hf⟩ := exists_three_first_basis a hp hq hs hl hn hd
  let c := Basis.mk hi.2 (span_three_last_eq_top a hp hq hs hl hn hd).ge
  obtain ⟨b, hb⟩ := exists_basis_coord_dotProduct f
  refine ⟨b, c, ?_, fun j ↦ Basis.mk_apply _ _ j⟩
  intro j u
  simpa only [hf] using hb j u

omit [Fintype J] in
/-- В согласованных базисах физический атомный тест есть coord_j⊗c_j. -/
theorem test_eq_basis_simple (a : J → PhysicalAtom alg)
    (b : Basis J K (P → K)) (c : Basis J K (S → K))
    (hb : ∀ j u, b.coord j u = u ⬝ᵥ (a j).first)
    (hc : ∀ j, c j = (a j).last) (j : J) :
    rowLinearEquiv (a j).test = (b.coord j).smulRight (c j) := by
  ext u s
  simp only [rowLinearEquiv_apply, vecMulLinear_apply, test, vecMul_vecMulVec,
    LinearMap.smulRight_apply, hb, hc, Pi.smul_apply, smul_eq_mul]

variable [Nonempty P] [Nonempty Q] [Nonempty S]

end ExactAlgorithm.PhysicalAtom
end MMRank
