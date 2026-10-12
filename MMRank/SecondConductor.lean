import MMRank.PhysicalConductor
import MMRank.CoefficientProductTransfer
import MMRank.NoZeroDivisorGrowth

/-! # Второй кондуктор и его совместимость с первым

Z=(B_F:A_F). Подъём α(A)z под β имеет физический образ в F.
Равенство поточечных произведений даёт закон C_d(A')B_z(A)=C_d(A)B_z(A').
-/

namespace MMRank.ExactAlgorithm

open Matrix Module

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] [Nonempty P]

/-- Физический подъём второго кондуктора, со значениями в матрицах с образом в F. -/
noncomputable def secondConductorMatrix (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F)) :
    matricesKilling (P := P) F →ₗ[K] matricesInto (S := S) F := by
  let e : matricesInto (S := S) F ≃ₗ[K] alg.toCoefficients.betaInto F :=
    Submodule.equivMapOfInjective _ alg.beta_injective _
  let f : matricesKilling (P := P) F →ₗ[K] alg.toCoefficients.betaInto F :=
    { toFun := fun A ↦ ⟨alg.toCoefficients.alpha A.val * z.val,
        (mem_conductor.mp z.property) _ (Submodule.mem_map.mpr ⟨A, A.property, rfl⟩)⟩
      map_add' := by intros; apply Subtype.ext; simp [add_mul]
      map_smul' := by intros; apply Subtype.ext; simp }
  exact e.symm.toLinearMap.comp f

@[simp] theorem beta_secondConductorMatrix (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F))
    (A : matricesKilling (P := P) F) :
    alg.toCoefficients.beta (alg.secondConductorMatrix F z A).val =
      alg.toCoefficients.alpha A.val * z.val := by
  simp only [secondConductorMatrix, LinearMap.comp_apply]
  exact Submodule.map_equivMapOfInjective_symm_apply _ _ _ _

/-- Закон двух кондукторов, ещё без гиперплоскости и единицы в A_F. -/
theorem two_conductor_law [Nonempty Q] (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F))
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F))
    (A A' : matricesKilling (P := P) F) :
    alg.conductorMatrix F d A' * (alg.secondConductorMatrix F z A).val =
      alg.conductorMatrix F d A * (alg.secondConductorMatrix F z A').val := by
  apply alg.mul_eq_of_beta_mul_gamma_eq
  rw [beta_secondConductorMatrix, beta_secondConductorMatrix,
    gamma_conductorMatrix, gamma_conductorMatrix]
  ring

/-- Линейная зависимость физического второго подъёма от слова z. -/
noncomputable def secondConductorWordMap (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K)) (A : matricesKilling (P := P) F) :
    conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F) →ₗ[K]
      matricesInto (S := S) F where
  toFun z := alg.secondConductorMatrix F z A
  map_add' z z' := by
    apply Subtype.ext
    apply alg.beta_injective
    simp [mul_add]
  map_smul' c z := by
    apply Subtype.ext
    apply alg.beta_injective
    simp

/-- Для ненулевого z тот же подъём инъективен по ограниченному входу A. -/
theorem secondConductorMatrix_injective_input [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn F)
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn F, ∀ b ∈ alg.toCoefficients.betaInto F,
      a * b = 0 → a = 0 ∨ b = 0)
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F))
    (hz : z.val ≠ 0) : Function.Injective (alg.secondConductorMatrix F z) := by
  intro A A' h
  apply Subtype.ext
  apply alg.alpha_injective
  apply sub_eq_zero.mp
  have hh := congrArg (fun B : matricesInto (S := S) F ↦ alg.toCoefficients.beta B.val) h
  rw [beta_secondConductorMatrix, beta_secondConductorMatrix] at hh
  have hm : alg.toCoefficients.alpha A.val - alg.toCoefficients.alpha A'.val ∈
      alg.toCoefficients.alphaOn F :=
    (alg.toCoefficients.alphaOn F).sub_mem (Submodule.mem_map.mpr ⟨A, A.property, rfl⟩)
      (Submodule.mem_map.mpr ⟨A', A'.property, rfl⟩)
  exact (hnz _ hm _ (conductor_le_of_one_mem _ _ h1 z.property)
    (by rw [sub_mul, hh, sub_self])).resolve_right hz

/-- Если C_d(A)=0, все значения первого семейства зануляются справа на B_z(A). -/
theorem two_conductor_annihilation [Nonempty Q] (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F))
    (z : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F))
    (A A' : matricesKilling (P := P) F) (hA : alg.conductorMatrix F d A = 0) :
    alg.conductorMatrix F d A' * (alg.secondConductorMatrix F z A).val = 0 := by
  rw [alg.two_conductor_law F d z A A', hA, Matrix.zero_mul]

end MMRank.ExactAlgorithm
