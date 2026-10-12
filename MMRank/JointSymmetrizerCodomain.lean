module

public import MMRank.JointSymmetrizers

@[expose] public section

/-! # Ограничение выхода семейства и выбор его координат

Инъективное вложение выхода сохраняет и отражает симметрию и NZ.
-/

namespace MMRank
variable {R U S Z W V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup S] [Module R S]
  [AddCommGroup Z] [Module R Z] [AddCommGroup W] [Module R W]
  [AddCommGroup V] [Module R V]

/-- B с образом в F переписано в координатах e:F≃V. -/
def codomainCoordinateFamily (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (F : Submodule R W) (hB : ∀ z u s, B z u s ∈ F) (e : F ≃ₗ[R] V) :
    Z →ₗ[R] U →ₗ[R] S →ₗ[R] V where
  toFun z :=
    { toFun := fun u ↦ e.toLinearMap.comp ((B z u).codRestrict F (hB z u))
      map_add' := by
        intro u v; apply LinearMap.ext; intro s
        change e ⟨B z (u + v) s, _⟩ = e ⟨B z u s, _⟩ + e ⟨B z v s, _⟩
        rw [← map_add]; congr 1; apply Subtype.ext; simp
      map_smul' := by
        intro a u; apply LinearMap.ext; intro s
        change e ⟨B z (a • u) s, _⟩ = a • e ⟨B z u s, _⟩
        rw [← map_smul]; congr 1; apply Subtype.ext; simp }
  map_add' := by
    intro z w; apply LinearMap.ext; intro u; apply LinearMap.ext; intro s
    change e ⟨B (z + w) u s, _⟩ = e ⟨B z u s, _⟩ + e ⟨B w u s, _⟩
    rw [← map_add]; congr 1; apply Subtype.ext; simp
  map_smul' := by
    intro a z; apply LinearMap.ext; intro u; apply LinearMap.ext; intro s
    change e ⟨B (a • z) u s, _⟩ = a • e ⟨B z u s, _⟩
    rw [← map_smul]; congr 1; apply Subtype.ext; simp

theorem codomainCoordinateFamily_recover (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (F : Submodule R W) (hB : ∀ z u s, B z u s ∈ F) (e : F ≃ₗ[R] V)
    (z : Z) (u : U) (s : S) :
    (e.symm (codomainCoordinateFamily B F hB e z u s)).val = B z u s := by
  change (e.symm (e ⟨B z u s, _⟩)).val = _
  rw [e.symm_apply_apply]

theorem jointSymmetrizer_codomainCoordinateFamily
    (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (F : Submodule R W) (hB : ∀ z u s, B z u s ∈ F) (e : F ≃ₗ[R] V) :
    jointSymmetrizer (codomainCoordinateFamily B F hB e) = jointSymmetrizer B := by
  ext M
  constructor
  · intro h z u v
    have hh := congrArg (fun x ↦ (e.symm x).val) (h z u v)
    simpa only [codomainCoordinateFamily_recover] using hh
  · intro h z u v
    apply e.symm.injective
    apply Subtype.ext
    simpa only [codomainCoordinateFamily_recover] using h z u v

theorem codomainCoordinateFamily_nz
    (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W)
    (F : Submodule R W) (hB : ∀ z u s, B z u s ∈ F) (e : F ≃ₗ[R] V)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0) :
    ∀ z u, codomainCoordinateFamily B F hB e z u = 0 → z = 0 ∨ u = 0 := by
  intro z u h
  apply hnz z u
  apply LinearMap.ext
  intro s
  have hh := congrArg (fun g : S →ₗ[R] V ↦ (e.symm (g s)).val) h
  simpa only [codomainCoordinateFamily_recover, LinearMap.zero_apply, map_zero,
    Submodule.coe_zero] using hh

end MMRank
