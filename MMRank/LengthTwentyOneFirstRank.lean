module

public import MMRank.LocalReplacementRanks
public import MMRank.FirstRankGrowthExclusion
public import MMRank.ThreeProfileExclusion
public import MMRank.FourAtomResidualExclusion

@[expose] public section

/-! # Общая21 с одним ранговым потенциалом

Минимальный первый столбец запрещает
рост одним обменом. При нулевом росте применяется трёхатомный бюджет,
а четыре атома исключаются единым остаточным аргументом.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K I : Type*} [Field K] [Fintype I]

section AlgClosed
variable [IsAlgClosed K]

/-- В минимальном представителе общая нормировка имеет нулевой рост. -/
theorem IsFirstRankMinimal.exists_zero_growth_normalization
    {alg : ExactAlgorithm K (Fin 3) (Fin 3) (Fin 3) I}
    (hmin : alg.IsFirstRankMinimal) (hl : Fintype.card I ≤ 20) :
    ∃ u : I → Kˣ, ∃ h : NormalizedHyperplaneCore (alg.rescale u),
      let M := (alg.rescale u).toCoefficients.alphaOn h.F
      let D := conductor (alg.rescale u).toCoefficients.gamma.range M
      M * D = D ∧ 3 ≤ finrank K D := by
  have hn := alg.nonzeroTerms_of_length_twenty rfl rfl rfl
    (Nat.le_antisymm hl (alg.length_bound_twenty rfl rfl rfl))
  obtain ⟨u, h, η, hη, hF, hcol⟩ :=
    alg.exists_normalized_hyperplane_with_columns hn (by decide)
  let a := alg.rescale u
  let M := a.toCoefficients.alphaOn h.F
  let D := conductor a.toCoefficients.gamma.range M
  have hb := a.critical_atom_dimension_bounds_direct h rfl rfl rfl hl
  change 3 ≤ finrank K D ∧ finrank K D ≤ finrank K (M * D) ∧
    finrank K (M * D) ≤ 5 ∧ _ at hb
  refine ⟨u, h, ?_, hb.1⟩
  by_cases he : finrank K (M * D) = finrank K D
  · exact (Submodule.eq_of_le_of_finrank_eq
      (le_mul_of_one_mem M D h.one_mem) he.symm).symm
  have hg : finrank K (M * D) = finrank K D + 1 := by
    have hlarge : 5 ≤ finrank K (M * D) → 4 ≤ finrank K D :=
      fun hh ↦ (hb.2.2.2.2.2 hh).1
    omega
  have hmina : a.IsFirstRankMinimal := (alg.isFirstRankMinimal_rescale_iff u).mpr hmin
  exact (hmina.growth_one_impossible rfl rfl rfl hl η hη hcol
    (by simpa only [← hF] using h.one_mem)
    (by rw [← hF]; exact hg)).elim

/-- Алгоритма длины20 нет: минимум существует по натуральности потенциала. -/
theorem no_length_twenty_by_first_rank_descent
    (alg : ExactAlgorithm K (Fin 3) (Fin 3) (Fin 3) (Fin 20)) : False := by
  obtain ⟨e, hmin⟩ := alg.exists_first_rank_minimal
  obtain ⟨u, h, he, hdlo⟩ := hmin.exists_zero_growth_normalization (by decide)
  let a := e.rescale u
  change 3 ≤ finrank K (conductor a.toCoefficients.gamma.range
    (a.toCoefficients.alphaOn h.F)) at hdlo
  have hdhi : finrank K (conductor a.toCoefficients.gamma.range
      (a.toCoefficients.alphaOn h.F)) ≤ 3 := by
    by_contra hn
    obtain ⟨atoms, hatoms⟩ := a.exists_physical_atoms_of_zero_growth h rfl rfl rfl
      (by decide) he 4 (by omega)
    exact a.four_physical_atoms_impossible_by_residual rfl h.nonzero_terms atoms hatoms
  exact a.zero_growth_three_profile_impossible h rfl rfl rfl (by decide) he
    (Nat.le_antisymm hdhi hdlo)
end AlgClosed

/-- Нижняя21 над произвольным полем; минимальность выбрана внутри доказательства. -/
theorem length_bound_twenty_one_by_first_rank_descent {P Q S : Type*}
    [Fintype P] [Fintype Q] [Fintype S]
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3) :
    21 ≤ Fintype.card I := by
  let e := alg.relabel (Fintype.equivFinOfCardEq hp) (Fintype.equivFinOfCardEq hq)
    (Fintype.equivFinOfCardEq hs)
  have hh := e.length_gt_of_no_normalized_algClosure (by decide) (by decide) 20
    (fun a _ ↦ a.no_length_twenty_by_first_rank_descent)
  omega

end MMRank.ExactAlgorithm
