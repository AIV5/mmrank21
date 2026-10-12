module

public import MMRank.CoefficientRescaling
public import MMRank.PointWordPhysical

@[expose] public section

/-! # Нормировка единицы без общего положения

Выбор вне конечного семейства ядер и компенсированное масштабирование.
Точность, ненулевость V/W и общность направления не требуются.
-/
namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [Field K] [Infinite K]
  [Fintype P] [Fintype Q] [Fintype I] [Nonempty Q]

/-- Ненулевые U допускают нормировку на
одной гиперплоскости. Размеры произвольны; Q непусто, I может быть пустым. -/
theorem Coefficients.exists_rescale_one_mem_hyperplane (d : Coefficients K P Q S I) (hn : ∀ i, d.U i ≠ 0) :
    ∃ η : Q → K, η ≠ 0 ∧ ∃ u : I → Kˣ,
      1 ∈ (d.rescale u).alphaOn (coordinateHyperplane η) := by
  classical
  let L : Option I → Submodule K (Q → K) := Option.elim' ⊥ (fun i ↦ (d.U i).mulVecLin.ker)
  have hL : ∀ i, L i ≠ ⊤ := by
    intro i
    cases i with
    | none => exact bot_ne_top
    | some i =>
      intro he
      have hz : (d.U i).mulVecLin = 0 := LinearMap.ker_eq_top.mp he
      apply hn i
      ext p q
      have hh := congrArg (fun f : (Q → K) →ₗ[K] (P → K) ↦ f (Pi.single q 1) p) hz
      simpa [mulVecLin_apply] using hh
  obtain ⟨η, hη⟩ := Submodule.exists_forall_notMem_of_forall_ne_top L hL
  have hη0 : η ≠ 0 := by simpa [L] using hη none
  refine ⟨η, hη0, d.exists_rescale_one_mem_alphaOn _ ?_⟩
  intro i
  have hi : d.U i *ᵥ η ≠ 0 := hη (some i)
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hi
  refine ⟨d.alpha (hyperplaneInput η (Pi.single p 1)).val,
    ⟨_, (hyperplaneInput η (Pi.single p 1)).property, rfl⟩, ?_⟩
  rw [Coefficients.alpha_hyperplaneInput_apply]
  simpa using hp
end MMRank
