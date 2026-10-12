module

public import MMRank.ConductorStabilizer
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Group.Indicator

@[expose] public section

/-!
# Координатные сечения и перенос разложений

Сечение N по s состоит из слов N, зануляющихся вне s. Это не ограничение
слов на s. Проектор сохраняет N лишь при явно указанной гипотезе.
В математической записи xπ_s; в Lean coordinateProjection R s x.
Каноничность или связность блоков в этом модуле не утверждается.
-/

namespace MMRank

section Semiring

variable (R : Type*) [CommSemiring R] {ι : Type*}

/-- Зануление координат вне s. -/
noncomputable def coordinateProjection (s : Set ι) : (ι → R) →ₗ[R] (ι → R) := by
  classical
  exact LinearMap.pi fun i ↦ if i ∈ s then LinearMap.proj i else 0

@[simp] theorem coordinateProjection_apply (s : Set ι) (x : ι → R) (i : ι) :
    coordinateProjection R s x i = s.indicator x i := by
  classical
  by_cases hi : i ∈ s <;> simp [coordinateProjection, hi]

/-- Внутреннее координатное сечение, не проекция произвольного слова N. -/
def coordinateSection (N : Submodule R (ι → R)) (s : Set ι) : Submodule R (ι → R) :=
  N ⊓ Submodule.pi sᶜ (fun _ ↦ ⊥)

variable {R}

@[simp] theorem mem_coordinateSection {N : Submodule R (ι → R)} {s : Set ι}
    {x : ι → R} : x ∈ coordinateSection R N s ↔ x ∈ N ∧ ∀ i ∉ s, x i = 0 := by
  simp [coordinateSection, Submodule.mem_pi]

theorem coordinateProjection_eq_self {s : Set ι} {x : ι → R}
    (hx : ∀ i ∉ s, x i = 0) : coordinateProjection R s x = x := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [hi, hx]

theorem coordinateProjection_add_compl (s : Set ι) (x : ι → R) :
    coordinateProjection R s x + coordinateProjection R sᶜ x = x := by
  simpa only [funext_iff, Pi.add_apply, coordinateProjection_apply] using
    congrFun (Set.indicator_self_add_compl s x)

/-- Проекция есть поточечное умножение на координатный идемпотент. -/
theorem coordinateProjection_eq_mul (s : Set ι) (x : ι → R) :
    coordinateProjection R s x = x * coordinateProjection R s 1 := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

theorem coordinateProjection_mul_right (s : Set ι) (x y : ι → R) :
    coordinateProjection R s (x * y) = x * coordinateProjection R s y := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [hi]

/-- Стабильность проектора эквивалентна принадлежности идемпотента (N:N). -/
theorem coordinateProjection_stable_iff (N : Submodule R (ι → R)) (s : Set ι) :
    (∀ x ∈ N, coordinateProjection R s x ∈ N) ↔
      coordinateProjection R s 1 ∈ conductor N N := by
  simp only [mem_conductor, ← coordinateProjection_eq_mul]

theorem coordinateProjection_map_eq_section (N : Submodule R (ι → R)) (s : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection R s x ∈ N) :
    N.map (coordinateProjection R s) = coordinateSection R N s := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_coordinateSection.mpr ⟨hs x hx, by intro i hi; simp [hi]⟩
  · intro x hx
    obtain ⟨hx, hz⟩ := mem_coordinateSection.mp hx
    exact ⟨x, hx, coordinateProjection_eq_self hz⟩

theorem coordinateSection_disjoint (N : Submodule R (ι → R)) (s : Set ι) :
    Disjoint (coordinateSection R N s) (coordinateSection R N sᶜ) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  obtain ⟨_, hx⟩ := mem_coordinateSection.mp hx
  obtain ⟨_, hy⟩ := mem_coordinateSection.mp hy
  ext i
  by_cases hi : i ∈ s
  · exact hy i (by simpa using hi)
  · exact hx i hi

/-- Два устойчивых дополнительных координатных проектора дают прямую сумму. -/
theorem coordinateSection_sup_compl (N : Submodule R (ι → R)) (s : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection R s x ∈ N)
    (ht : ∀ x ∈ N, coordinateProjection R sᶜ x ∈ N) :
    coordinateSection R N s ⊔ coordinateSection R N sᶜ = N := by
  classical
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro x hx
  rw [← coordinateProjection_add_compl s x]
  apply Submodule.add_mem_sup
  · exact mem_coordinateSection.mpr ⟨hs x hx, by intro i hi; simp [hi]⟩
  · exact mem_coordinateSection.mpr ⟨ht x hx, by intro i hi; simp [hi]⟩

/-- Образ произведения под координатным проектором. Стабильность не нужна. -/
theorem coordinateProjection_map_mul (M D : Submodule R (ι → R)) (s : Set ι) :
    (M * D).map (coordinateProjection R s) = M * D.map (coordinateProjection R s) := by
  simp only [Submodule.mul_eq_map₂, Submodule.map_map₂, Submodule.map₂_map_right]
  congr 1
  ext x y
  exact congrFun (coordinateProjection_mul_right s x y) _

/-- В насыщенной паре координатный проектор сохраняет D тогда и только тогда,
когда он сохраняет E. -/
theorem saturated_coordinateProjection_stable_iff (M N : Submodule R (ι → R))
    (s : Set ι) :
    (∀ x ∈ conductor N M, coordinateProjection R s x ∈ conductor N M) ↔
      ∀ x ∈ M * conductor N M, coordinateProjection R s x ∈ M * conductor N M := by
  rw [coordinateProjection_stable_iff, coordinateProjection_stable_iff,
    conductor_saturated_stabilizer]

/-- Для устойчивого сечения насыщенной пары E_s=M D_s. -/
theorem saturated_coordinateSection_mul (M N : Submodule R (ι → R)) (s : Set ι)
    (hs : ∀ x ∈ M * conductor N M,
      coordinateProjection R s x ∈ M * conductor N M) :
    coordinateSection R (M * conductor N M) s = M * coordinateSection R (conductor N M) s := by
  rw [← coordinateProjection_map_eq_section _ _ hs, coordinateProjection_map_mul,
    coordinateProjection_map_eq_section _ _
      ((saturated_coordinateProjection_stable_iff M N s).mpr hs)]

/-- При 1∈M пространства D и MD имеют общий координатный носитель. -/
theorem product_coord_nonzero_iff (M D : Submodule R (ι → R))
    (hM : (1 : ι → R) ∈ M) (i : ι) :
    (∃ x ∈ M * D, x i ≠ 0) ↔ ∃ d ∈ D, d i ≠ 0 := by
  constructor
  · contrapose!
    intro h x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm d hd
      change m i * d i = 0
      rw [h d hd, mul_zero]
    · intro x y hx hy
      change x i + y i = 0
      rw [hx, hy, add_zero]
  · rintro ⟨d, hd, hi⟩
    exact ⟨d, le_mul_of_one_mem M D hM hd, hi⟩

end Semiring

section Ring

variable {R : Type*} [CommRing R] {ι : Type*}

/-- Над кольцом устойчивость дополнительного проектора следует из устойчивости исходного. -/
theorem coordinateProjection_compl_stable (N : Submodule R (ι → R)) (s : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection R s x ∈ N) :
    ∀ x ∈ N, coordinateProjection R sᶜ x ∈ N := by
  intro x hx
  convert N.sub_mem hx (hs x hx) using 1
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm, coordinateProjection_add_compl])

end Ring

section Field

variable {K : Type*} [Field K] {ι : Type*}

theorem finrank_coordinateSection_add_compl (N : Submodule K (ι → K))
    [FiniteDimensional K N] (s : Set ι)
    (hs : ∀ x ∈ N, coordinateProjection K s x ∈ N) :
    Module.finrank K (coordinateSection K N s) +
      Module.finrank K (coordinateSection K N sᶜ) = Module.finrank K N := by
  let : FiniteDimensional K (coordinateSection K N s) :=
    Submodule.finiteDimensional_of_le (show coordinateSection K N s ≤ N from inf_le_left)
  let : FiniteDimensional K (coordinateSection K N sᶜ) :=
    Submodule.finiteDimensional_of_le (show coordinateSection K N sᶜ ≤ N from inf_le_left)
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (coordinateSection K N s) (coordinateSection K N sᶜ)
  rw [coordinateSection_sup_compl N s hs (coordinateProjection_compl_stable N s hs),
    (coordinateSection_disjoint N s).eq_bot, finrank_bot, add_zero] at h
  exact h.symm

end Field

end MMRank
