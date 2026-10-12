import MMRank.PhysicalConductor

/-! # Координатный и физический ранги отдельного слова кондуктора -/

namespace MMRank.ExactAlgorithm

open Module

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι] [Nonempty Q]

/-- Координатный образ семейства C_d равен A_F d. -/
theorem conductorMatrix_range_map_gamma (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F)) :
    (alg.conductorMatrix F d).range.map alg.toCoefficients.gamma =
      (alg.toCoefficients.alphaOn F).map (LinearMap.mulRight K d.val) := by
  ext w
  constructor
  · rintro ⟨C, ⟨A, rfl⟩, rfl⟩
    exact ⟨alg.toCoefficients.alpha A.val, Submodule.mem_map.mpr ⟨A, A.property, rfl⟩,
      (alg.gamma_conductorMatrix F d A).symm⟩
  · rintro ⟨a, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨alg.conductorMatrix F d ⟨A, hA⟩, ⟨⟨A, hA⟩, rfl⟩,
      alg.gamma_conductorMatrix F d ⟨A, hA⟩⟩

/-- Размерности A_F d и физического семейства совпадают для любого F. -/
theorem finrank_conductorMatrix_range (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F)) :
    finrank K (alg.conductorMatrix F d).range =
      finrank K ((alg.toCoefficients.alphaOn F).map (LinearMap.mulRight K d.val)) := by
  rw [← alg.conductorMatrix_range_map_gamma F d]
  exact (Submodule.equivMapOfInjective _ alg.gamma_injective _).finrank_eq

end MMRank.ExactAlgorithm
