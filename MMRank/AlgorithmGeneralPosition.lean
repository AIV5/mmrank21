import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import MMRank.RankFactorization
import MMRank.Algorithm
import MMRank.TraceDuality

/-!
# Полная лемма выбора F для точного алгоритма

К ранговым условиям добавлено порождение всеми Vᵢ с tr(UᵢA) ≠ 0.
Свидетели неполноты выбираются для конечного семейства подмножеств индексов;
один общий выбор F работает сразу для всех A с ker A ≤ F.
Минимальность, длина двадцать и специальный формат не используются.
-/

namespace MMRank

open Module
open scoped BigOperators

namespace ExactAlgorithm

variable {K P Q S ι : Type*} [Field K] [Infinite K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

omit [Infinite K] in
/-- Свидетели неполноты, не лежащие в F, обеспечивают порождение
активными Vᵢ. Бесконечность поля и размерность F не требуются. -/
theorem active_span_eq_top_of_annihilator_avoid
    (d : ExactAlgorithm K P Q S ι) (F : Submodule K (Q → K))
    (havoid : ∀ J : Set ι, Submodule.span K (d.V '' J) ≠ ⊤ →
      ∃ B : Matrix S Q K, (∀ i ∈ J, Matrix.trace (d.V i * B) = 0) ∧
        ¬ B.vecMulLinear.range ≤ F)
    (A : Matrix Q P K) (hA : A.vecMulLinear.ker ≤ F) :
    Submodule.span K (d.V '' {i | Matrix.trace (d.U i * A) ≠ 0}) = ⊤ := by
  by_contra hspan
  obtain ⟨B, hv, hB⟩ := havoid _ hspan
  have hmul : B * A = 0 := by
    rw [d.exact_formula]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : Matrix.trace (d.U i * A) = 0
    · simp [hi]
    · simp [hv i hi]
  apply hB
  apply le_trans ?_ hA
  apply LinearMap.range_le_ker_iff.mpr
  rw [← rowLinear_mul B A, hmul]
  ext x p
  simp

end ExactAlgorithm

end MMRank
