import MMRank.AlgorithmGenericDirections

/-! # Данные нормированной общей гиперплоскости

Пакет используется после выбора поля, а не переносится автоматически
из исходного поля. Минимальность алгоритма не предполагается.
-/

namespace MMRank.ExactAlgorithm
open Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Гиперплоскость с нормировкой, полными носителями и усиленным NZ.
Размерности образов и ограниченное NZ выводятся отдельно из точности. -/
structure NormalizedHyperplaneCore (alg : ExactAlgorithm K P Q S ι) where
  F : Submodule K (Q → K)
  codim_one : finrank K F + 1 = Fintype.card Q
  nonzero_terms : alg.toCoefficients.NonzeroTerms
  one_mem : (1 : ι → K) ∈ alg.toCoefficients.alphaOn F
  alpha_support : ∀ i, ∃ a ∈ alg.toCoefficients.alphaOn F, a i ≠ 0
  beta_support : ∀ i, ∃ b ∈ alg.toCoefficients.betaInto F, b i ≠ 0
  gamma_support : ∀ i, ∃ c ∈ alg.toCoefficients.gamma.range, c i ≠ 0
  full_nz : ∀ a ∈ alg.toCoefficients.alphaOn F, ∀ b ∈ alg.toCoefficients.beta.range,
    a * b = 0 → a = 0 ∨ b = 0
  generic_column : ∃ η : Q → K, η ≠ 0 ∧ F = coordinateHyperplane η ∧
    MatrixColumnGeneric alg.U η

/-- Сильный резервный пакет добавляет общность направлений и точные ограниченные ранги.
Текущий корень21 использует только NormalizedHyperplaneCore. -/
structure NormalizedHyperplane (alg : ExactAlgorithm K P Q S ι)
    extends NormalizedHyperplaneCore alg where
  generic_direction : ∃ η : Q → K, η ≠ 0 ∧ F = coordinateHyperplane η ∧
    MatrixDirectionGeneric alg.U η
  beta_rank : ∀ i, finrank K ((alg.V i).vecMulLinear.domRestrict F).range =
    min (alg.V i).rank (Fintype.card Q - 1)

namespace NormalizedHyperplaneCore

/-- Ограниченное NZ следует из усиленного, поскольку B_F⊆im β. -/
theorem restricted_nz {alg : ExactAlgorithm K P Q S ι} (h : NormalizedHyperplaneCore alg) :
    ∀ a ∈ alg.toCoefficients.alphaOn h.F, ∀ b ∈ alg.toCoefficients.betaInto h.F,
      a * b = 0 → a = 0 ∨ b = 0 := by
  intro a ha b hb hab
  obtain ⟨B, _, rfl⟩ := hb
  exact h.full_nz a ha _ ⟨B, rfl⟩ hab

end NormalizedHyperplaneCore

namespace NormalizedHyperplane
/-- Сильный пакет забывает ранговое общее положение. -/
theorem restricted_nz {alg : ExactAlgorithm K P Q S ι} (h : NormalizedHyperplane alg) :
    ∀ a ∈ alg.toCoefficients.alphaOn h.F, ∀ b ∈ alg.toCoefficients.betaInto h.F,
      a * b = 0 → a = 0 ∨ b = 0 := h.toNormalizedHyperplaneCore.restricted_nz

end NormalizedHyperplane

/-- Калибровка уже выбранной поддержанной гиперплоскости.
Общие дополнительные условия на η выбираются до этого перехода. -/
theorem exists_rescale_normalized_hyperplane_of_supported [Infinite K]
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (hn : alg.toCoefficients.NonzeroTerms)
    (η : Q → K) (hη : η ≠ 0) (hgen : MatrixColumnGeneric alg.U η)
    (ha : ∀ i, ∃ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η), a i ≠ 0)
    (hb : ∀ i, ∃ b ∈ alg.toCoefficients.betaInto (coordinateHyperplane η), b i ≠ 0)
    (hfull : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ b ∈ alg.toCoefficients.beta.range, a * b = 0 → a = 0 ∨ b = 0) :
    ∃ u : ι → Kˣ, ∃ h : NormalizedHyperplaneCore (alg.rescale u), h.F = coordinateHyperplane η := by
  let F := coordinateHyperplane η
  obtain ⟨u, h1⟩ := alg.toCoefficients.exists_rescale_one_mem_alphaOn F ha
  let e := alg.rescale u
  have hα : e.toCoefficients.alphaOn F = (alg.toCoefficients.alphaOn F).map
      (coordinateScale (fun i ↦ (u i)⁻¹)).toLinearMap :=
    alg.toCoefficients.alphaOn_rescale u F
  have hγ : e.toCoefficients.gamma.range = alg.toCoefficients.gamma.range.map
      (coordinateScale u).toLinearMap := alg.toCoefficients.range_gamma_rescale u
  refine ⟨u, ⟨F, finrank_coordinateHyperplane_add_one η hη,
    alg.nonzeroTerms_rescale u hn, h1, ?_, hb, ?_, ?_,
    η, hη, rfl, (matrixColumnGeneric_smul_iff alg.U
      (fun i ↦ ((u i)⁻¹ : Kˣ).val) (fun i ↦ Units.ne_zero _) η).mpr hgen⟩,
    rfl⟩
  · intro i
    rw [hα]
    exact (coordinateScale_support_iff _ _ i).mpr (ha i)
  · intro i
    rw [hγ]
    exact (coordinateScale_support_iff _ _ i).mpr
      ((traceCoordinates_coord_nonzero_iff alg.W i).mpr (hn i).2.2)
  · change ∀ a ∈ e.toCoefficients.alphaOn F, ∀ b ∈ alg.toCoefficients.beta.range,
      a * b = 0 → a = 0 ∨ b = 0
    rw [hα]
    exact (coordinateScale_no_zero_divisors_iff _ _ _).mpr hfull

/-- Поддержанная нормировка с общностью столбцового ядра.
Выбор направлений и точные ограниченные ранги для неё не нужны. -/
theorem exists_normalized_hyperplane_with_columns [Infinite K]
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (hn : alg.toCoefficients.NonzeroTerms)
    (hq : 2 ≤ Fintype.card Q) :
    ∃ u : ι → Kˣ, ∃ h : NormalizedHyperplaneCore (alg.rescale u),
      ∃ η : Q → K, η ≠ 0 ∧ h.F = coordinateHyperplane η ∧
        MatrixColumnGeneric (alg.rescale u).U η := by
  obtain ⟨η, hη, hc, ha, hb, hnz⟩ := alg.exists_supported_column_hyperplane_basic hn hq
  obtain ⟨u, h, hF⟩ := alg.exists_rescale_normalized_hyperplane_of_supported hn η hη hc ha hb hnz
  exact ⟨u, h, η, hη, hF, (matrixColumnGeneric_smul_iff alg.U
    (fun i ↦ ((u i)⁻¹ : Kˣ).val) (fun i ↦ Units.ne_zero _) η).mpr hc⟩

/-- Минимальный пакет, достаточный выбранному доказательству21. -/
theorem exists_normalized_hyperplane_core [Infinite K]
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (hn : alg.toCoefficients.NonzeroTerms)
    (hq : 2 ≤ Fintype.card Q) :
    ∃ u : ι → Kˣ, Nonempty (NormalizedHyperplaneCore (alg.rescale u)) := by
  obtain ⟨u, h, _⟩ := alg.exists_normalized_hyperplane_with_columns hn hq
  exact ⟨u, ⟨h⟩⟩

end MMRank.ExactAlgorithm
