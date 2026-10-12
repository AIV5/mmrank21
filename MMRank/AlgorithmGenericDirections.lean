import MMRank.GenericHyperplane
import MMRank.CoefficientRescaling
import MMRank.FullBetaNoZeroDivisors
import MMRank.SupportedTestSpace

/-! # Совместный выбор направлений, носителей и усиленного NZ -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K] [Infinite K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  [Nonempty Q]

omit [Infinite K] in
/-- Полные носители, усиленное NZ и общность столбцового ядра совместимы
с любыми конечными ненулевыми полиномиальными условиями. -/
theorem polynomial_open_supported_columns_with
    (d : ExactAlgorithm K P Q S I) (hn : d.toCoefficients.NonzeroTerms)
    (hq : 2 ≤ Fintype.card Q) {L : Type*} [Fintype L]
    (f : L → MvPolynomial Q K) (hf : ∀ l, f l ≠ 0) :
    ∃ g : MvPolynomial Q K, g ≠ 0 ∧ ∀ η, MvPolynomial.eval η g ≠ 0 →
      η ≠ 0 ∧ MatrixColumnGeneric d.U η ∧
      (∀ i, ∃ a ∈ d.toCoefficients.alphaOn (coordinateHyperplane η), a i ≠ 0) ∧
      (∀ i, ∃ b ∈ d.toCoefficients.betaInto (coordinateHyperplane η), b i ≠ 0) ∧
      (∀ a ∈ d.toCoefficients.alphaOn (coordinateHyperplane η),
        ∀ b ∈ d.toCoefficients.beta.range, a * b = 0 → a = 0 ∨ b = 0) ∧
      ∀ l, MvPolynomial.eval η (f l) ≠ 0 := by
  classical
  let Bad := {J : Set I // Submodule.span K (d.V '' J) ≠ ⊤}
  have hw (j : Bad) : ∃ B : Matrix S Q K,
      B ≠ 0 ∧ ∀ i ∈ j.val, trace (d.V i * B) = 0 := by
    obtain ⟨B, hB, hv⟩ := exists_nonzero_trace_annihilator
      (Submodule.span K (d.V '' j.val)) j.property
    exact ⟨B, hB, fun i hi ↦ hv _ (Submodule.subset_span ⟨i, hi, rfl⟩)⟩
  choose B hB hv using hw
  let T₀ : Sum (Sum I I) Bad → Submodule K (Q → K) :=
    Sum.elim (Sum.elim (fun i ↦ (d.U i).vecMulLinear.range)
      (fun i ↦ (d.V i).vecMulLinear.ker)) (fun j ↦ (B j).vecMulLinear.range)
  obtain ⟨g₀, hg₀, hgood⟩ := polynomial_open_column_hyperplane d.U T₀
  obtain ⟨g₁, hg₁, h₁⟩ := polynomial_open_finset f hf
  refine ⟨g₀ * g₁, mul_ne_zero hg₀ hg₁, ?_⟩
  intro η hηg
  have hh := mul_ne_zero_iff.mp
    (show MvPolynomial.eval η g₀ * MvPolynomial.eval η g₁ ≠ 0 by simpa using hηg)
  obtain ⟨hη, hcore, hF, hT⟩ := hgood η hh.1
  let F := coordinateHyperplane η
  change finrank K F + 1 = Fintype.card Q at hF
  have havoid (j : Bad) : ¬ (B j).vecMulLinear.range ≤ F := by
    intro hle
    have hh := hT (Sum.inr j)
    change finrank K (F ⊓ (B j).vecMulLinear.range : Submodule K (Q → K)) =
      finrank K (B j).vecMulLinear.range - 1 at hh
    rw [inf_eq_right.mpr hle] at hh
    have hz : finrank K (B j).vecMulLinear.range = 0 := by omega
    exact hB j ((matrix_rank_eq_zero_iff _).mp
      ((matrix_rank_eq_finrank_rowRange _).trans hz))
  refine ⟨hη, hcore, ?_, ?_, ?_, h₁ η hh.2⟩
  · intro i
    apply (d.toCoefficients.alphaOn_coord_nonzero_iff F i).mpr
    intro hle
    have hh := hT (Sum.inl (Sum.inl i))
    change finrank K (F ⊓ (d.U i).vecMulLinear.range : Submodule K (Q → K)) =
      finrank K (d.U i).vecMulLinear.range - 1 at hh
    rw [inf_eq_right.mpr hle] at hh
    have hz : finrank K (d.U i).vecMulLinear.range = 0 := by omega
    exact (hn i).1 ((matrix_rank_eq_zero_iff _).mp
      ((matrix_rank_eq_finrank_rowRange _).trans hz))
  · intro i
    apply (d.toCoefficients.betaInto_coord_nonzero_iff F i).mpr
    intro hle
    have hh := hT (Sum.inl (Sum.inr i))
    change finrank K (F ⊓ (d.V i).vecMulLinear.ker : Submodule K (Q → K)) =
      finrank K (d.V i).vecMulLinear.ker - 1 at hh
    rw [inf_eq_left.mpr hle] at hh
    have hr := (d.V i).vecMulLinear.finrank_range_add_finrank_ker
    rw [← matrix_rank_eq_finrank_rowRange, Module.finrank_fintype_fun_eq_card] at hr
    exact (hn i).2.1 ((matrix_rank_eq_zero_iff _).mp (by omega))
  · intro a ha b hb hab
    exact d.toCoefficients.hyperplane_full_beta_no_zero_divisors F hF
      (fun A hA ↦ d.active_span_eq_top_of_annihilator_avoid F
        (fun J hJ ↦ ⟨B ⟨J, hJ⟩, hv ⟨J, hJ⟩, havoid ⟨J, hJ⟩⟩) A hA) ha hb hab

/-- Минимальный поддержанный выбор: общность столбцов, два носителя и NZ.
Условия направлений, рангов V и образов тестов сюда не входят. -/
theorem exists_supported_column_hyperplane_basic
    (d : ExactAlgorithm K P Q S I) (hn : d.toCoefficients.NonzeroTerms)
    (hq : 2 ≤ Fintype.card Q) :
    ∃ η : Q → K, η ≠ 0 ∧ MatrixColumnGeneric d.U η ∧
      (∀ i, ∃ a ∈ d.toCoefficients.alphaOn (coordinateHyperplane η), a i ≠ 0) ∧
      (∀ i, ∃ b ∈ d.toCoefficients.betaInto (coordinateHyperplane η), b i ≠ 0) ∧
      (∀ a ∈ d.toCoefficients.alphaOn (coordinateHyperplane η),
        ∀ b ∈ d.toCoefficients.beta.range, a * b = 0 → a = 0 ∨ b = 0) := by
  obtain ⟨g, hg, hgood⟩ := d.polynomial_open_supported_columns_with hn hq
    (fun j : Fin 0 ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)
  obtain ⟨η, hηg⟩ := exists_eval_all_ne_zero (fun _ : Unit ↦ g) (fun _ ↦ hg)
  obtain ⟨hη, hc, ha, hb, hnz, _⟩ := hgood η (hηg ())
  exact ⟨η, hη, hc, ha, hb, hnz⟩

end MMRank.ExactAlgorithm
