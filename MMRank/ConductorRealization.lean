import MMRank.Conductor
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Реализация кондуктора через линейное вложение

Если N является образом инъективного f, произведение m d имеет единственный
прообраз. Его линейная оболочка реализует насыщенную оболочку M(N:M).
-/

namespace MMRank

variable {R A V : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V]

/-- Билинейный подъём произведения m d через инъективное f. -/
noncomputable def conductorLift (f : V →ₗ[R] A) (hf : Function.Injective f)
    (M : Submodule R A) : M →ₗ[R] conductor f.range M →ₗ[R] V where
  toFun m :=
    (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp
      (show conductor f.range M →ₗ[R] f.range from
      { toFun := fun d ↦ ⟨m.val * d.val, (mem_conductor.mp d.property) m.val m.property⟩
        map_add' := fun d e ↦ Subtype.ext (mul_add _ _ _)
        map_smul' := fun r d ↦ Subtype.ext (mul_smul_comm r m.val d.val) })
  map_add' m n := by
    ext d
    apply hf
    simp [map_add, add_mul]
  map_smul' r m := by
    ext d
    apply hf
    simp [map_smul]

@[simp] theorem map_conductorLift (f : V →ₗ[R] A) (hf : Function.Injective f)
    (M : Submodule R A) (m : M) (d : conductor f.range M) :
    f (conductorLift f hf M m d) = m.val * d.val := by
  simp [conductorLift]

/-- Единственность подъёма; выбор базиса и расширение поля не нужны. -/
theorem conductorLift_unique (f : V →ₗ[R] A) (hf : Function.Injective f)
    (M : Submodule R A) (m : M) (d : conductor f.range M) {v : V}
    (hv : f v = m.val * d.val) : v = conductorLift f hf M m d :=
  hf (hv.trans (map_conductorLift f hf M m d).symm)

/-- Физическая насыщенная оболочка, в отличие от её координатного образа. -/
def conductorPhysicalSpace (f : V →ₗ[R] A) (M : Submodule R A) : Submodule R V :=
  (M * conductor f.range M).comap f

theorem conductorLift_mem_physicalSpace (f : V →ₗ[R] A) (hf : Function.Injective f)
    (M : Submodule R A) (m : M) (d : conductor f.range M) :
    conductorLift f hf M m d ∈ conductorPhysicalSpace f M := by
  change f _ ∈ M * conductor f.range M
  rw [map_conductorLift]
  exact Submodule.mul_mem_mul m.property d.property

/-- Все физические элементы насыщенной оболочки порождены поднятыми произведениями. -/
theorem conductorPhysicalSpace_eq_span (f : V →ₗ[R] A) (hf : Function.Injective f)
    (M : Submodule R A) :
    conductorPhysicalSpace f M = Submodule.span R
      (Set.range fun p : M × conductor f.range M ↦ conductorLift f hf M p.1 p.2) := by
  apply le_antisymm
  · intro v hv
    change f v ∈ M * conductor f.range M at hv
    have hh : ∀ w ∈ M * conductor f.range M, ∀ v, f v = w →
        v ∈ Submodule.span R (Set.range fun p : M × conductor f.range M ↦
          conductorLift f hf M p.1 p.2) := by
      intro w hw
      induction hw using Submodule.mul_induction_on' with
      | mem_mul_mem m hm d hd =>
        intro v hv
        rw [conductorLift_unique f hf M ⟨m, hm⟩ ⟨d, hd⟩ hv]
        exact Submodule.subset_span ⟨(⟨m, hm⟩, ⟨d, hd⟩), rfl⟩
      | add w hw z hz ihw ihz =>
        intro v hv
        obtain ⟨v₁, hv₁⟩ := mul_conductor_le M f.range hw
        obtain ⟨v₂, hv₂⟩ := mul_conductor_le M f.range hz
        have he : v = v₁ + v₂ := hf (by rw [hv, map_add, hv₁, hv₂])
        rw [he]
        exact Submodule.add_mem _ (ihw v₁ hv₁) (ihz v₂ hv₂)
    exact hh _ hv v rfl
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨m, d⟩, rfl⟩
    exact conductorLift_mem_physicalSpace f hf M m d

/-- Прообраз насыщенной оболочки имеет ту же размерность, что её координатный образ. -/
theorem finrank_conductorPhysicalSpace {K A V : Type*} [Field K] [CommRing A]
    [Algebra K A] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] A) (hf : Function.Injective f) (M : Submodule K A) :
    Module.finrank K (conductorPhysicalSpace f M) =
      Module.finrank K (M * conductor f.range M) :=
  (Submodule.comap_equiv_self_of_inj_of_le hf (mul_conductor_le M f.range)).finrank_eq

end MMRank
