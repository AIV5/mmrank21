module

public import MMRank.MatrixColumnCore
public import Mathlib.GroupTheory.CosetCover

@[expose] public section

/-! # Общность гиперплоскости одновременно с различением направлений -/

namespace MMRank
open Matrix Module MvPolynomial
variable {K P Q I J : Type*} [Field K] [Fintype Q]

/-- Размерность координатной гиперплоскости над произвольным полем. -/
theorem finrank_coordinateHyperplane_add_one (η : Q → K) (hη : η ≠ 0) :
    finrank K (coordinateHyperplane η) + 1 = Fintype.card Q := by
  classical
  have hf : dotProductBilin K K η ≠ 0 := by
    intro hz
    apply hη
    ext q
    have hh := DFunLike.congr_fun hz (Pi.single q 1)
    simpa [dotProduct, Pi.single_apply] using hh
  change finrank K ((dotProductBilin K K η).ker) + 1 = Fintype.card Q
  exact (Module.Dual.finrank_ker_add_one_of_ne_zero hf).trans (by simp)

/-- Если форма не зануляется на ненулевом T, пересечение теряет одно
измерение; нулевое T обрабатывается без ненужного условия. -/
theorem finrank_coordinateHyperplane_inf (η : Q → K) (T : Submodule K (Q → K))
    (hT : T ≠ ⊥ → ¬ T ≤ coordinateHyperplane η) :
    finrank K (coordinateHyperplane η ⊓ T : Submodule K (Q → K)) = finrank K T - 1 := by
  by_cases hz : T = ⊥
  · rw [hz, inf_bot_eq, finrank_bot]
  let f := (dotProductBilin K K η).domRestrict T
  have hf : f ≠ 0 := by
    intro hh
    apply hT hz
    intro x hx
    exact DFunLike.congr_fun hh ⟨x, hx⟩
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  change finrank K ((dotProductBilin K K η).domRestrict T).ker + 1 = finrank K T at hd
  rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq T,
    Submodule.map_comap_subtype, inf_comm] at hd
  change finrank K (coordinateHyperplane η ⊓ T : Submodule K (Q → K)) + 1 = finrank K T at hd
  omega

/-- Общая гиперплоскость совместима с любыми конечными ненулевыми
полиномиальными условиями. Матричное семейство для этого выбора не нужно. -/
theorem polynomial_open_hyperplane_constraints [Nonempty Q] [Fintype J]
    {L : Type*} [Fintype L] (T : J → Submodule K (Q → K))
    (f : L → MvPolynomial Q K) (hf : ∀ l, f l ≠ 0) :
    ∃ g : MvPolynomial Q K, g ≠ 0 ∧ ∀ η, eval η g ≠ 0 →
      η ≠ 0 ∧
      finrank K (coordinateHyperplane η) + 1 = Fintype.card Q ∧
      (∀ j, finrank K (coordinateHyperplane η ⊓ T j : Submodule K (Q → K)) =
        finrank K (T j) - 1) ∧ ∀ l, eval η (f l) ≠ 0 := by
  classical
  let Good := {j : J // T j ≠ ⊥}
  choose v hv hv0 using fun j : Good ↦ (Submodule.ne_bot_iff (T j)).mp j.property
  let q₀ : Q := Classical.arbitrary Q
  let a : Option Good → MvPolynomial Q K := fun j ↦ match j with
    | none => X q₀
    | some j => matrixVectorPolynomial (Matrix.of (fun _ : Unit ↦ v j)) ()
  have ha (j : Option Good) : a j ≠ 0 := by
    cases j with
    | none => exact X_ne_zero q₀
    | some j =>
      intro hz
      obtain ⟨q, hq⟩ : ∃ q, v j q ≠ 0 := by simpa [funext_iff] using hv0 j
      have hh := congrArg (eval (Pi.single q 1)) hz
      apply hq
      simpa [a, matrixVectorPolynomial, Pi.single_apply] using hh
  obtain ⟨g₀, hg₀, h₀⟩ := polynomial_open_finset a ha
  obtain ⟨g₁, hg₁, h₁⟩ := polynomial_open_finset f hf
  refine ⟨g₀ * g₁, mul_ne_zero hg₀ hg₁, ?_⟩
  intro η hη
  have hh := mul_ne_zero_iff.mp (show eval η g₀ * eval η g₁ ≠ 0 by simpa using hη)
  have hη0 : η ≠ 0 := by
    intro hz
    have hn := h₀ η hh.1 none
    simp [a, hz] at hn
  refine ⟨hη0, finrank_coordinateHyperplane_add_one η hη0, ?_, h₁ η hh.2⟩
  intro j
  apply finrank_coordinateHyperplane_inf
  intro hj hle
  have hn := h₀ η hh.1 (some ⟨j, hj⟩)
  apply hn
  simp only [a]
  rw [matrixVectorPolynomial_eval]
  change v ⟨j, hj⟩ ⬝ᵥ η = 0
  rw [dotProduct_comm]
  exact hle (hv ⟨j, hj⟩)

/-- Общность столбцового ядра и конечных пересечений выбирается без
условия различения матричных направлений. -/
theorem polynomial_open_column_hyperplane [Nonempty Q] [Fintype I] [Fintype J]
    (U : I → Matrix P Q K) (T : J → Submodule K (Q → K)) :
    ∃ g : MvPolynomial Q K, g ≠ 0 ∧ ∀ η, eval η g ≠ 0 →
      η ≠ 0 ∧ MatrixColumnGeneric U η ∧
      finrank K (coordinateHyperplane η) + 1 = Fintype.card Q ∧
      ∀ j, finrank K (coordinateHyperplane η ⊓ T j : Submodule K (Q → K)) =
        finrank K (T j) - 1 := by
  obtain ⟨f, hf, hgood⟩ := polynomial_open_matrixSubspaceGeneric U
    (fun G : Set I ↦ matrixColumnCore (Submodule.span K (U '' G)))
  obtain ⟨g, hg, h⟩ := polynomial_open_hyperplane_constraints T
    (fun _ : Unit ↦ f) (fun _ ↦ hf)
  refine ⟨g, hg, ?_⟩
  intro η hηg
  obtain ⟨hη, hF, hT, hfη⟩ := h η hηg
  exact ⟨hη, fun G i _ ↦ hgood η (hfη ()) G i, hF, hT⟩

end MMRank
