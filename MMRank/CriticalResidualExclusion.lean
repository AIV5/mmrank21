import MMRank.CriticalResidualSliceModel
import MMRank.FourDimensionalSlice
import MMRank.DiagonalThreeSlice
import MMRank.ResidualRayContradiction

/-! # Пять независимых тестов нельзя реконструировать восемью простыми срезами
Критическое следствие над любым полем.
-/
namespace MMRank
open Matrix Module
variable {K I L : Type*} [Field K] [Fintype I] [AddCommGroup L] [Module K L]

/-- Единый остаточный запрет для четырёх атомов333: пять выходов и восемь членов. -/
theorem not_eight_rank_one_reconstruction
    (b : Basis (Fin 5) K L) (w : I → L) (hc : Fintype.card I = 8)
    (A : Fin 5 → I → Matrix (Fin 3) (Fin 3) K)
    (hr : ∀ j i, (A j i).rank ≤ 1)
    (h : ∀ j X, ∑ i, trace (X * A j i) • w i = trace X • b j) : False := by
  classical
  let : FiniteDimensional K L := Module.Finite.of_basis b
  obtain ⟨hk, μ, hp, hs, hmodel⟩ := exists_critical_residual_slice_model b w hc A hr h
  let F := Fintype.linearCombination K w
  apply residual_ray_good_bad_contradiction b F hk.le μ hp hc
  intro j
  obtain ⟨Z, hz, ha, h1, hlo, hhi, hm⟩ := hmodel j
  have hlin := trace_reconstruction_linear_forms w (b j) (A j) (h j)
  by_cases hd : finrank K (Submodule.span K (Set.range (A j))) = 3
  · have hrZ : finrank K Z.range = 2 := by omega
    rcases diagonal_three_slice_dichotomy w (b j) (b.ne_zero j) μ hs Z hz hrZ
      (fun i ↦ A j i 0 0) (A j) ha (hr j) h1 hd hlin with
      ⟨C, H, ht⟩ | ⟨i, ht, hsep⟩
    · left
      refine ⟨C, H, ?_⟩
      intro a
      simpa [ThreeRayCover.activeOutput_eq_span, ThreeRayCover.activeIndices, F]
        using ht a
    · right
      exact ⟨i, hsep, by simpa [F] using ht⟩
  · have hd4 : finrank K (Submodule.span K (Set.range (A j))) = 4 := by omega
    obtain ⟨i, hsep, ht⟩ := four_dimensional_slice_separated_output w (b j) (A j)
      (hr j) (by omega) hlin μ hp Z hz ha h1 hd4 hm
    exact Or.inr ⟨i, hsep, by simpa [F] using ht⟩

end MMRank
