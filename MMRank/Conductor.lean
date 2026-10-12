module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Кондуктор и насыщенная пара

conductor N M означает (N : M), то есть {x | Mx ⊆ N}.
Это библиотечное деление подмодулей, а не факторпространство.
Базовые свойства действуют в любой коммутативной алгебре над полукольцом.
-/

namespace MMRank

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Кондуктор (N : M); порядок аргументов соответствует этой записи. -/
abbrev conductor (N M : Submodule R A) : Submodule R A := N / M

theorem mem_conductor {N M : Submodule R A} {x : A} :
    x ∈ conductor N M ↔ ∀ m ∈ M, m * x ∈ N := by
  simp only [conductor, Submodule.mem_div_iff_forall_mul_mem, mul_comm]

/-- Кондуктор — наибольшее X, для которого MX ⊆ N. -/
theorem mul_le_iff_le_conductor (M X N : Submodule R A) :
    M * X ≤ N ↔ X ≤ conductor N M := by
  rw [Submodule.le_div_iff_mul_le, mul_comm]

theorem mul_conductor_le (M N : Submodule R A) : M * conductor N M ≤ N :=
  (mul_le_iff_le_conductor _ _ _).mpr le_rfl

/-- Монотонность по пространству цели. -/
theorem conductor_mono {N N' M : Submodule R A} (h : N ≤ N') :
    conductor N M ≤ conductor N' M := fun _ hx _ hm ↦ h (hx _ hm)

/-- Единица в M даёт X ⊆ MX. -/
theorem le_mul_of_one_mem (M X : Submodule R A) (hM : (1 : A) ∈ M) : X ≤ M * X := by
  intro x hx
  simpa using Submodule.mul_mem_mul hM hx

theorem conductor_le_of_one_mem (N M : Submodule R A) (hM : (1 : A) ∈ M) :
    conductor N M ≤ N :=
  (le_mul_of_one_mem M _ hM).trans (mul_conductor_le M N)

/-- Замена N на M(N:M) не меняет кондуктор. Единица для этого равенства не нужна. -/
theorem conductor_mul_conductor (M N : Submodule R A) :
    conductor (M * conductor N M) M = conductor N M := by
  apply le_antisymm (conductor_mono (mul_conductor_le M N))
  exact (mul_le_iff_le_conductor _ _ _).mp le_rfl

end MMRank
