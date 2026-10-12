import MMRank.AlgorithmReflection
import MMRank.CoefficientRescaling
import MMRank.PhysicalReindex
import Mathlib.Order.WellFounded

/-! # Минимум одной суммы рангов и допустимые нормировки -/
namespace MMRank.ExactAlgorithm
open Matrix
variable {K P Q S I J : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Fintype J]

/-- Минимальность только первого столбца среди точных алгоритмов того
же формата с тем же множеством индексов. -/
def IsFirstRankMinimal (alg : ExactAlgorithm K P Q S I) : Prop :=
  ∀ e : ExactAlgorithm K P Q S I, (∑ i, (alg.U i).rank) ≤ ∑ i, (e.U i).rank

/-- Из существования точного алгоритма данного формата следует
существование представителя с минимальной первой суммой рангов. -/
theorem exists_first_rank_minimal (alg : ExactAlgorithm K P Q S I) :
    ∃ e : ExactAlgorithm K P Q S I, e.IsFirstRankMinimal := by
  let : Nonempty (ExactAlgorithm K P Q S I) := ⟨alg⟩
  exact ⟨Function.argmin (fun e : ExactAlgorithm K P Q S I ↦ ∑ i, (e.U i).rank),
    fun e ↦ Nat.le_of_not_lt (Function.not_lt_argmin
      (fun a : ExactAlgorithm K P Q S I ↦ ∑ i, (a.U i).rank) e)⟩

/-- Компенсированная калибровка сохраняет все три индивидуальных ранга. -/
theorem ranks_rescale (alg : ExactAlgorithm K P Q S I) (u : I → Kˣ) (i : I) :
    ((alg.rescale u).U i).rank = (alg.U i).rank ∧
    ((alg.rescale u).V i).rank = (alg.V i).rank ∧
    ((alg.rescale u).W i).rank = (alg.W i).rank := by
  refine ⟨?_, rfl, ?_⟩
  · change (((u i)⁻¹ : Kˣ).val • alg.U i).rank = _
    exact rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (Units.ne_zero _))
  · change ((u i).val • alg.W i).rank = _
    exact rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (Units.ne_zero _))

/-- Калибровка не теряет и не создаёт минимальность первого столбца. -/
theorem isFirstRankMinimal_rescale_iff (alg : ExactAlgorithm K P Q S I) (u : I → Kˣ) :
    (alg.rescale u).IsFirstRankMinimal ↔ alg.IsFirstRankMinimal := by
  simp only [IsFirstRankMinimal, (alg.ranks_rescale u _).1]

variable {N : Type*} [Fintype N]

end MMRank.ExactAlgorithm
