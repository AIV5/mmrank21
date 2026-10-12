module

public import MMRank.JointSymmetrizerNZDimension
public import MMRank.PointWordSecondConductorCapacity
public import MMRank.RestrictedConductorBounds
public import MMRank.PhysicalConductorBounds
public import MMRank.LargeSaturationExclusion

@[expose] public section

/-! # Критические размерности из одного пространства симметризаторов

При z≥3 общий бюджет совместных симметризаторов даёт e≤1.
Начальные размерностные оценки тогда делают D одномерной собственной
прямой; ограничение z≤3 противоречит d+z≥5.
Случай e≥5,z=2 исключается факторизацией пространства совместных симметризаторов.
-/

namespace MMRank.ExactAlgorithm
open Module Matrix
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  [Nonempty P] [Nonempty Q] [Nonempty S]

omit [Nonempty Q] [Nonempty S] in
/-- Все физические значения B порождают пространство не меньшей размерности,
чем координатное произведение A_F Z. -/
theorem finrank_alpha_mul_secondConductor_le_family_span
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0) :
    finrank K (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
        (alg.toCoefficients.alphaOn (coordinateHyperplane η))) ≤
      finrank K ↥(⨆ z, (alg.secondConductorIntoFamily η z).range :
        Submodule K ((S → K) →ₗ[K] coordinateHyperplane η)) := by
  let E : Submodule K ((S → K) →ₗ[K] coordinateHyperplane η) :=
    ⨆ z, (alg.secondConductorIntoFamily η z).range
  have hm : alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
        (alg.toCoefficients.alphaOn (coordinateHyperplane η)) ≤
      E.map (alg.betaOnLinearInto (coordinateHyperplane η)) := by
    apply Submodule.mul_le.mpr
    intro a ha z hz
    obtain ⟨A, hA, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨u, hu⟩ := hyperplaneInput_surjective (P := P) η hη ⟨A, hA⟩
    refine ⟨alg.secondConductorIntoFamily η ⟨z, hz⟩ u, ?_, ?_⟩
    · exact (le_iSup (fun z ↦ (alg.secondConductorIntoFamily η z).range) ⟨z, hz⟩)
        ⟨u, rfl⟩
    · rw [alg.betaOnLinearInto_secondConductor, hu]
  exact (Submodule.finrank_mono hm).trans (Submodule.finrank_map_le _ _)

omit [Nonempty S] in
/-- Ограничение выхода в F сохраняет размерность пространства симметризаторов. -/
theorem saturated_finrank_le_jointSymmetrizer_into
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0) :
    finrank K (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range
        (alg.toCoefficients.alphaOn (coordinateHyperplane η))) ≤
      finrank K (jointSymmetrizer (alg.secondConductorIntoFamily η)) := by
  have he : jointSymmetrizer (alg.secondConductorIntoFamily η) =
      jointSymmetrizer (alg.hyperplaneSecondConductorFamily η) := by
    ext C
    constructor
    · intro h z u v
      exact congrArg Subtype.val (h z u v)
    · intro h z u v
      exact Subtype.ext (h z u v)
  rw [he]
  exact alg.saturated_finrank_le_jointSymmetrizer η hη

/-- При z≥3 физическое насыщение имеет размерность≤1.
Длина алгоритма здесь не ограничена. -/
theorem saturated_finrank_le_one_of_secondConductor_ge_three [IsAlgClosed K]
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ b ∈ alg.toCoefficients.betaInto (coordinateHyperplane η),
      a * b = 0 → a = 0 ∨ b = 0)
    (hZ : 3 ≤ finrank K (conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)))) :
    finrank K (alg.toCoefficients.alphaOn (coordinateHyperplane η) *
      conductor alg.toCoefficients.gamma.range
        (alg.toCoefficients.alphaOn (coordinateHyperplane η))) ≤ 1 := by
  have hF : finrank K (coordinateHyperplane η) = 2 := by
    have := finrank_coordinateHyperplane_add_one η hη
    omega
  have hz0 : conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) ≠ ⊥ := by
    intro hh
    rw [hh, finrank_bot] at hZ
    omega
  have hg := saturated_growth_of_noZeroDivisors _ _ h1 hz0 hnz
  have hm := alg.finrank_alphaOn (coordinateHyperplane η)
  rw [hp, hq, hF] at hm
  have hspan := alg.finrank_alpha_mul_secondConductor_le_family_span η hη
  have hh := finrank_jointSymmetrizer_le_one_of_nz_capacity
    (alg.secondConductorIntoFamily η) (hp.trans hs.symm) (by omega)
    (alg.secondConductorIntoFamily_nz η hη h1 hnz)
    (by simp only [hs, hF]; omega) (by simp only [hs, hF]; omega)
  exact (alg.saturated_finrank_le_jointSymmetrizer_into η hη).trans hh

/-- При длине≤20 второй кондуктор имеет размерность≤2.
Доказательство проходит через весь Σ, а не через точечность всех слов D. -/
theorem critical_secondConductor_le_two_direct [IsAlgClosed K]
    (alg : ExactAlgorithm K P Q S I) (h : NormalizedHyperplaneCore alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) :
    finrank K (conductor (alg.toCoefficients.betaInto h.F)
      (alg.toCoefficients.alphaOn h.F)) ≤ 2 := by
  by_contra! hz
  have hF : finrank K h.F = 2 := by have := h.codim_one; omega
  have hlow := alg.restricted_conductor_strengthened_bound h.F 1 (by omega)
    (by omega) h.one_mem (by simp [hp]) (by simp [hq, hs]) h.beta_support h.restricted_nz
  have hsum := alg.restricted_two_conductor_dimension_sum_bound h.F 1 (by omega)
    (by omega) h.one_mem (by simp [hp])
  have hsat := (alg.restricted_conductor_saturated_dimensions h.F h.one_mem).1
  simp only [hp, hq, hs] at hlow hsum
  obtain ⟨η, hη, heF⟩ := exists_coordinateHyperplane_of_finrank_add_one h.F h.codim_one
  have he := alg.saturated_finrank_le_one_of_secondConductor_ge_three hp hq hs η hη
    (heF ▸ h.one_mem) (heF ▸ h.restricted_nz) (heF ▸ hz)
  rw [← heF] at he
  have hd : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F) ≠ ⊥ := by
    intro hh
    rw [hh, finrank_bot] at hlow
    omega
  obtain ⟨w, hw, hw0⟩ := (conductor _ _).ne_bot_iff.mp hd
  have hwm : w ∈ alg.toCoefficients.alphaOn h.F *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F) :=
    le_mul_of_one_mem _ _ h.one_mem hw
  have he1 : finrank K (alg.toCoefficients.alphaOn h.F *
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn h.F)) = 1 := by omega
  have hew := eq_span_singleton_of_mem_of_finrank_eq_one he1 hwm hw0
  have hpw : IsPointWord (alg.toCoefficients.alphaOn h.F) w := by
    refine ⟨hw0, ?_⟩
    intro m hm
    have hh := Submodule.mul_mem_mul hm hw
    rw [hew, Submodule.mem_span_singleton] at hh
    obtain ⟨a, ha⟩ := hh
    exact ⟨a, ha.symm⟩
  have hzu := alg.secondConductor_finrank_le_three_of_point_word_direct h.F hs hF
    (by simp [hp, hq, hF]) h.one_mem h.restricted_nz ⟨w, hw⟩ hpw
  omega

/-- Прямые необходимые размеры с сохранением готового шага e≥5,z=2. -/
theorem critical_atom_dimension_bounds_direct [IsAlgClosed K]
    (alg : ExactAlgorithm K P Q S I) (h : NormalizedHyperplaneCore alg)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) :
    let M := alg.toCoefficients.alphaOn h.F
    let D := conductor alg.toCoefficients.gamma.range M
    let d := finrank K D
    let e := finrank K (M * D)
    let z := finrank K (conductor (alg.toCoefficients.betaInto h.F) M)
    3 ≤ d ∧ d ≤ e ∧ e ≤ 5 ∧ z ≤ 2 ∧ 5 ≤ d + z ∧
      (5 ≤ e → 4 ≤ d ∧ z ≤ 1) := by
  dsimp only
  have hF : finrank K h.F = 2 := by have := h.codim_one; omega
  have hsum := alg.restricted_two_conductor_dimension_sum_bound h.F 1 (by omega)
    (by omega) h.one_mem (by simp [hp])
  have hsat := (alg.restricted_conductor_saturated_dimensions h.F h.one_mem).1
  have hupp := alg.saturated_physical_length_bound_of_hyperplane h.F h.codim_one
  simp only [hp, hq, hs] at hsum hupp
  have hz := alg.critical_secondConductor_le_two_direct h hp hq hs hl
  refine ⟨by omega, hsat, by omega, hz, by omega, ?_⟩
  intro he
  have hz1 : finrank K (conductor (alg.toCoefficients.betaInto h.F)
      (alg.toCoefficients.alphaOn h.F)) ≤ 1 := by
    by_contra! hn
    have hh := alg.length_ge_twenty_one_of_large_saturation_second_two h hp hq hs he
      (by omega)
    omega
  exact ⟨by omega, hz1⟩

end MMRank.ExactAlgorithm
