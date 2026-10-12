module

public import MMRank.RestrictedInputs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

@[expose] public section

/-!
# Ограниченные коэффициентные пространства

A_F и B_F — образы пространств входов, а не множества матриц фиксированного ранга.
Ортогональное дополнение берётся относительно Σ xᵢyᵢ, без сопряжения.
-/

namespace MMRank

open Module
open scoped BigOperators

variable {K P Q S ι : Type*}
  [Fintype P] [Fintype Q] [Fintype S]

section Semiring

variable [CommSemiring K]

namespace Coefficients

/-- A_F = α{A : F ≤ ker A}. -/
noncomputable def alphaOn (d : Coefficients K P Q S ι) (F : Submodule K (Q → K)) :
    Submodule K (ι → K) := (matricesKilling F).map d.alpha

/-- B_F = β{B : im B ≤ F}. -/
def betaInto (d : Coefficients K P Q S ι) (F : Submodule K (Q → K)) :
    Submodule K (ι → K) := (matricesInto F).map d.beta

end Coefficients

namespace ExactAlgorithm

variable [Fintype ι]

/-- Поточечное произведение a ∈ A_F и b ∈ B_F ортогонально всему образу γ. -/
theorem restricted_triple_sum_eq_zero (d : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    {a b z : ι → K} (ha : a ∈ d.toCoefficients.alphaOn F)
    (hb : b ∈ d.toCoefficients.betaInto F) (hz : z ∈ d.toCoefficients.gamma.range) :
    ∑ i, a i * b i * z i = 0 := by
  obtain ⟨A, hA, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨B, hB, rfl⟩ := Submodule.mem_map.mp hb
  obtain ⟨C, rfl⟩ := hz
  change ∑ i, Matrix.trace (d.U i * A) * Matrix.trace (d.V i * B) *
    Matrix.trace (d.W i * C) = 0
  rw [← d.trace_identity A B C, Matrix.mul_assoc, mul_eq_zero_of_restricted F A B hA hB]
  simp

/-- Линейная оболочка произведений A_F B_F содержится в Ccal^⊥. -/
theorem restricted_product_le_orthogonal (d : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K)) :
    d.toCoefficients.alphaOn F * d.toCoefficients.betaInto F ≤
      d.toCoefficients.gamma.range.orthogonalBilin (dotProductBilin K K) := by
  apply Submodule.mul_le.mpr
  intro a ha b hb
  apply Submodule.mem_orthogonalBilin.mpr
  intro z hz
  have h := d.restricted_triple_sum_eq_zero F ha hb hz
  simpa [dotProductBilin, dotProduct, mul_comm] using h

end ExactAlgorithm

end Semiring

namespace ExactAlgorithm

variable [Field K] [Fintype ι]

/-- Размерность A_F для любого F, без общего положения. -/
theorem finrank_alphaOn [Nonempty S] (d : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K)) :
    finrank K (d.toCoefficients.alphaOn F) =
      Fintype.card P * (Fintype.card Q - finrank K F) := by
  rw [Coefficients.alphaOn, ← (Submodule.equivMapOfInjective _ d.alpha_injective _).finrank_eq]
  exact finrank_matricesKilling F

/-- Размерность B_F для любого F, без общего положения. -/
theorem finrank_betaInto [Nonempty P] (d : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K)) :
    finrank K (d.toCoefficients.betaInto F) = Fintype.card S * finrank K F := by
  rw [Coefficients.betaInto, ← (Submodule.equivMapOfInjective _ d.beta_injective _).finrank_eq]
  exact finrank_matricesInto F

/-- Три размерности при заданной коразмерности; Ccal — полный образ γ. -/
theorem restricted_dimensions [Nonempty P] [Nonempty Q] [Nonempty S]
    (d : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (c : ℕ) (hc : c ≤ Fintype.card Q) (hF : finrank K F = Fintype.card Q - c) :
    finrank K (d.toCoefficients.alphaOn F) = Fintype.card P * c ∧
    finrank K (d.toCoefficients.betaInto F) = Fintype.card S * (Fintype.card Q - c) ∧
    finrank K d.toCoefficients.gamma.range = Fintype.card P * Fintype.card S := by
  rw [d.finrank_alphaOn, d.finrank_betaInto, d.finrank_range_gamma, hF,
    Nat.sub_sub_self hc, Nat.mul_comm (Fintype.card S) (Fintype.card P)]
  exact ⟨rfl, rfl, rfl⟩

end ExactAlgorithm

end MMRank
