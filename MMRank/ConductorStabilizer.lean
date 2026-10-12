import MMRank.Conductor

/-!
# Мультипликативные стабилизаторы насыщенной пары

Стабилизатор здесь — подмодуль (N:N) всех множителей, сохраняющих N,
а не группа обратимых преобразований. Единица в M не требуется.
-/

namespace MMRank

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Множитель, сохраняющий D, сохраняет MD. -/
theorem conductor_self_le_product (M D : Submodule R A) :
    conductor D D ≤ conductor (M * D) (M * D) := by
  intro z hz
  rw [mem_conductor] at hz ⊢
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm d hd
    simpa [mul_assoc] using Submodule.mul_mem_mul hm (hz d hd)
  · intro x y hx hy
    simpa [add_mul] using (M * D).add_mem hx hy

/-- Множитель, сохраняющий E, сохраняет кондуктор (E:M). -/
theorem conductor_self_le_conductor (M E : Submodule R A) :
    conductor E E ≤ conductor (conductor E M) (conductor E M) := by
  intro z hz
  rw [mem_conductor] at hz ⊢
  intro d hd
  rw [mem_conductor] at hd ⊢
  intro m hm
  simpa [mul_assoc] using hz (m * d) (hd m hm)

/-- Для D=(N:M), E=MD стабилизаторы совпадают. -/
theorem conductor_saturated_stabilizer (M N : Submodule R A) :
    conductor (conductor N M) (conductor N M) =
      conductor (M * conductor N M) (M * conductor N M) := by
  apply le_antisymm (conductor_self_le_product M _)
  simpa only [conductor_mul_conductor] using
    conductor_self_le_conductor M (M * conductor N M)

end MMRank
