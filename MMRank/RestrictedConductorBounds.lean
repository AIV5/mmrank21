module

public import MMRank.RestrictedTwoConductorBound
public import MMRank.TwoDirectionGrowth

@[expose] public section

/-!
# Кондукторные оценки для ограниченных коэффициентных пространств

Предполагается нормировка 1 ∈ A_F.
Начальные оценки используют только точность, единицу, размерности и ортогональность.
Завершающая усиленная оценка при pc=3 дополнительно использует полный носитель
и отсутствие делителей нуля, уже полученные для нормированных пространств.
-/

namespace MMRank.ExactAlgorithm

open Module

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- d ≤ e ≤ ps для D=(Ccal:A_F), E=A_F D; D≠0 не предполагается. -/
theorem restricted_conductor_saturated_dimensions [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn F) :
    let M := alg.toCoefficients.alphaOn F
    let D := conductor alg.toCoefficients.gamma.range M
    finrank K D ≤ finrank K (M * D) ∧
      finrank K (M * D) ≤ Fintype.card P * Fintype.card S := by
  have h := finrank_conductor_saturated_pair
    (alg.toCoefficients.alphaOn F) alg.toCoefficients.gamma.range h1
  simpa only [alg.finrank_range_gamma, Nat.mul_comm (Fintype.card S) (Fintype.card P)] using h

/-- Усиление через границу физических отношений: при pc=3 и s(q−c)≥2
получено 3ps+2≤d+2(ℓ−s(q−c)). Носитель и отсутствие делителей нуля —
явные условия, обеспеченные нормированным пакетом; бесконечность поля здесь не нужна. -/
theorem restricted_conductor_strengthened_bound [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (c : ℕ) (hc : c ≤ Fintype.card Q) (hF : finrank K F = Fintype.card Q - c)
    (h1 : (1 : ι → K) ∈ alg.toCoefficients.alphaOn F) (hpc : Fintype.card P * c = 3)
    (ht : 2 ≤ Fintype.card S * (Fintype.card Q - c))
    (hsupp : ∀ i, ∃ b ∈ alg.toCoefficients.betaInto F, b i ≠ 0)
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn F, ∀ b ∈ alg.toCoefficients.betaInto F,
      a * b = 0 → a = 0 ∨ b = 0) :
    3 * (Fintype.card P * Fintype.card S) + 2 ≤
      finrank K (conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F)) +
        2 * (Fintype.card ι - Fintype.card S * (Fintype.card Q - c)) := by
  obtain ⟨hM, hB, hN⟩ := alg.restricted_dimensions F c hc hF
  have hM3 : finrank K (alg.toCoefficients.alphaOn F) = 3 := hM.trans hpc
  have hB2 : 2 ≤ finrank K (alg.toCoefficients.betaInto F) := by omega
  have horth := (le_coordinateOrthogonal_mul_iff (alg.toCoefficients.alphaOn F)
    (alg.toCoefficients.betaInto F) alg.toCoefficients.gamma.range).mpr
      (alg.restricted_product_le_orthogonal F)
  have hh := conductor_bound_of_noZeroDivisors (alg.toCoefficients.alphaOn F)
    alg.toCoefficients.gamma.range (alg.toCoefficients.betaInto F) h1 hM3 horth hB2 hsupp hnz
  rw [hB, hN] at hh
  exact hh

end MMRank.ExactAlgorithm
