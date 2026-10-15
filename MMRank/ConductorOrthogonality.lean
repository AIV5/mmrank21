import MMRank.ConductorGrowth
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Двойственность кондуктора и роста для коэффициентных функций

Спаривание — Σ xᵢyᵢ без сопряжения. Произведение и кондуктор используют
готовые операции над подмодулями. Никакой положительной определённости нет.
-/

namespace MMRank

open Module

variable {K ι : Type*} [Fintype ι]

section Semiring

variable [CommSemiring K]

/-- Ортогональное дополнение для стандартного билинейного спаривания функций. -/
abbrev coordinateOrthogonal (N : Submodule K (ι → K)) : Submodule K (ι → K) :=
  N.orthogonalBilin (dotProductBilin K K)

/-- (MN)^⊥ = (N^⊥ : M). -/
theorem coordinateOrthogonal_mul (M N : Submodule K (ι → K)) :
    coordinateOrthogonal (M * N) = conductor (coordinateOrthogonal N) M := by
  ext z
  rw [mem_conductor]
  constructor
  · intro hz m hm n hn
    have h := hz (m * n) (Submodule.mul_mem_mul hm hn)
    simpa [dotProductBilin, dotProduct, mul_assoc, mul_left_comm, mul_comm] using h
  · intro hz
    change M * N ≤ ((dotProductBilin K K).flip z).ker
    apply Submodule.mul_le.mpr
    intro m hm n hn
    have h := hz m hm n hn
    change (m * n) ⬝ᵥ z = 0
    simpa [dotProductBilin, dotProduct, mul_assoc, mul_left_comm, mul_comm] using h

/-- Перенос множителя между аргументами ортогональности. -/
theorem le_coordinateOrthogonal_mul_iff (M B N : Submodule K (ι → K)) :
    B ≤ coordinateOrthogonal (M * N) ↔ M * B ≤ coordinateOrthogonal N := by
  rw [coordinateOrthogonal_mul, ← mul_le_iff_le_conductor]

/-- Невырожденность спаривания функций проверяется на координатных единицах. -/
theorem coordinatePairing_nondegenerate :
    (dotProductBilin K K : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K).Nondegenerate := by
  classical
  constructor
  · intro x hx
    ext i
    have h := hx (Pi.single i 1)
    simpa [dotProductBilin] using h
  · intro x hx
    ext i
    have h := hx (Pi.single i 1)
    simpa [dotProductBilin] using h

end Semiring

section Field

variable [Field K]

/-- dim N^⊥ = |ι| − dim N над любым полем. -/
theorem finrank_coordinateOrthogonal (N : Submodule K (ι → K)) :
    finrank K (coordinateOrthogonal N) = Fintype.card ι - finrank K N := by
  have h := LinearMap.BilinForm.finrank_orthogonal
    (B := (dotProductBilin K K : (ι → K) →ₗ[K] (ι → K) →ₗ[K] K))
    (coordinatePairing_nondegenerate (K := K) (ι := ι)) N
  change finrank K (coordinateOrthogonal N) = finrank K (ι → K) - finrank K N at h
  rwa [Module.finrank_pi] at h

/-- Ортогональность MB ⊆ N^⊥ ограничивает размерность MN. -/
theorem finrank_product_add_le_of_orthogonal (M B N : Submodule K (ι → K))
    (h : M * B ≤ coordinateOrthogonal N) :
    finrank K (M * N) + finrank K B ≤ Fintype.card ι := by
  have hb := Submodule.finrank_mono ((le_coordinateOrthogonal_mul_iff M B N).mpr h)
  rw [finrank_coordinateOrthogonal] at hb
  have hm := (M * N).finrank_le
  rw [Module.finrank_pi] at hm
  omega

end Field

end MMRank
