module

public import MMRank.SecondConductor
public import MMRank.NormalizedFamily

@[expose] public section

/-! # Линейные физические семейства первого и второго кондукторов -/

set_option backward.isDefEq.respectTransparency false

namespace MMRank.ExactAlgorithm

open Module Matrix

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] [Nonempty Q]

/-- Первый физический кондуктор как семейство отображений на строках. -/
noncomputable def conductorLinearFamily (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F)) :
    matricesKilling (P := P) F →ₗ[K] ((P → K) →ₗ[K] (S → K)) :=
  rowLinearEquiv.toLinearMap.comp (alg.conductorMatrix F d)

@[simp] theorem conductorLinearFamily_apply (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F))
    (A : matricesKilling (P := P) F) :
    alg.conductorLinearFamily F d A = (alg.conductorMatrix F d A).vecMulLinear := by
  simp [conductorLinearFamily]

variable [Nonempty P]

/-- Второй подъём билинеен по слову z и ограниченному входу A. -/
noncomputable def secondConductorLinearFamily (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K)) :
    conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F) →ₗ[K]
      (matricesKilling (P := P) F →ₗ[K] ((S → K) →ₗ[K] (Q → K))) where
  toFun z := rowLinearEquiv.toLinearMap.comp
    ((matricesInto (S := S) F).subtype.comp (alg.secondConductorMatrix F z))
  map_add' z z' := by
    apply LinearMap.ext
    intro A
    change rowLinearEquiv ((alg.secondConductorWordMap F A) (z + z')).val =
      rowLinearEquiv ((alg.secondConductorWordMap F A) z).val +
        rowLinearEquiv ((alg.secondConductorWordMap F A) z').val
    simp only [map_add, Submodule.coe_add]
  map_smul' a z := by
    apply LinearMap.ext
    intro A
    change rowLinearEquiv ((alg.secondConductorWordMap F A) (a • z)).val =
      a • rowLinearEquiv ((alg.secondConductorWordMap F A) z).val
    simp only [map_smul, Submodule.coe_smul]

omit [Nonempty Q] in
@[simp] theorem secondConductorLinearFamily_apply (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F))
    (A : matricesKilling (P := P) F) :
    alg.secondConductorLinearFamily F z A = (alg.secondConductorMatrix F z A).val.vecMulLinear := by
  simp [secondConductorLinearFamily]

omit [Nonempty Q] in
theorem secondConductorLinearFamily_range_le (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F))
    (A : matricesKilling (P := P) F) : (alg.secondConductorLinearFamily F z A).range ≤ F := by
  rw [secondConductorLinearFamily_apply]
  exact (mem_matricesInto F _).mp (alg.secondConductorMatrix F z A).property

theorem conductorLinearFamilies_compatible (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F))
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F))
    (A A' : matricesKilling (P := P) F) :
    (alg.secondConductorLinearFamily F z A).comp (alg.conductorLinearFamily F d A') =
      (alg.secondConductorLinearFamily F z A').comp (alg.conductorLinearFamily F d A) := by
  simp only [secondConductorLinearFamily_apply, conductorLinearFamily_apply]
  rw [← rowLinear_mul, ← rowLinear_mul, alg.two_conductor_law]

end MMRank.ExactAlgorithm
