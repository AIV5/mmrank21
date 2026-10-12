import MMRank.ConductorSeparableFactor
import MMRank.DiagonalCoefficientLaw

/-! # Второй кондуктор со значениями в самой гиперплоскости -/
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Nonempty P] [Nonempty Q]

/-- Ограничение значений второго семейства, без выбора базиса F. -/
noncomputable def secondConductorIntoFamily (alg : ExactAlgorithm K P Q S I) (η : Q → K) :
    conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) →ₗ[K]
      (P → K) →ₗ[K] (S → K) →ₗ[K] coordinateHyperplane η where
  toFun z :=
    { toFun := fun u ↦ (alg.hyperplaneSecondConductorFamily η z u).codRestrict _
        (alg.hyperplaneSecondConductorFamily_mem η z u)
      map_add' := by intros; ext s q; simp
      map_smul' := by intros; ext s q; simp }
  map_add' := by intros; ext u s q; simp
  map_smul' := by intros; ext u s q; simp

omit [Nonempty Q] in
@[simp] theorem coe_secondConductorIntoFamily
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (z) (u : P → K) (s : S → K) :
    (alg.secondConductorIntoFamily η z u s).val = alg.hyperplaneSecondConductorFamily η z u s := rfl

omit [Nonempty Q] in
theorem secondConductorIntoFamily_nz [Nonempty S]
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ b ∈ alg.toCoefficients.betaInto (coordinateHyperplane η), a * b = 0 → a = 0 ∨ b = 0) :
    ∀ z u, alg.secondConductorIntoFamily η z u = 0 → z = 0 ∨ u = 0 := by
  intro z u he
  apply alg.hyperplaneSecondConductorFamily_nz η hη h1 hnz z u
  ext s q
  exact congrArg (fun T : (S → K) →ₗ[K] coordinateHyperplane η ↦ (T s).val q) he

/-- Каждый физический тест кондуктора симметризует также семейство в F. -/
theorem test_mem_jointSymmetrizer_into
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (T : (P → K) →ₗ[K] (S → K))
    (hT : alg.toCoefficients.gamma (rowLinearEquiv.symm T) ∈
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) :
    T ∈ jointSymmetrizer (alg.secondConductorIntoFamily η) := by
  have ht : T ∈ jointSymmetrizer (alg.hyperplaneSecondConductorFamily η) := by
    apply alg.conductorPhysicalSpace_le_jointSymmetrizer η hη
    refine ⟨rowLinearEquiv.symm T, ?_, rowLinearEquiv.apply_symm_apply T⟩
    exact le_mul_of_one_mem _ _ h1 hT
  intro z u v
  apply Subtype.ext
  exact ht z u v

/-- Оценка β на отображении в F; используется исходная следовая форма. -/
noncomputable def betaOnLinearInto (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (Q → K)) : ((S → K) →ₗ[K] F) →ₗ[K] (I → K) where
  toFun T := alg.toCoefficients.beta (rowLinearEquiv.symm (F.subtype.comp T))
  map_add' := by intros; simp [LinearMap.comp_add]
  map_smul' := by intros; simp [LinearMap.comp_smul]

omit [Nonempty Q] in
@[simp] theorem betaOnLinearInto_secondConductor
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (z) (u : P → K) :
    alg.betaOnLinearInto (coordinateHyperplane η) (alg.secondConductorIntoFamily η z u) =
      alg.toCoefficients.alpha (hyperplaneInput η u).val * z.val := by
  change alg.toCoefficients.beta (rowLinearEquiv.symm
    ((coordinateHyperplane η).subtype.comp (alg.secondConductorIntoFamily η z u))) = _
  have he : (coordinateHyperplane η).subtype.comp (alg.secondConductorIntoFamily η z u) =
      rowLinearEquiv (alg.secondConductorMatrix (coordinateHyperplane η) z (hyperplaneInput η u)).val := by
    rfl
  rw [he, rowLinearEquiv.symm_apply_apply, beta_secondConductorMatrix]

end MMRank.ExactAlgorithm
