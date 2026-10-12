module

public import MMRank.TraceSliceSpace

@[expose] public section

/-! # Восемь срезов и пятиэлементный базис выхода
Общий остаточный контракт,
специализированный к единственному критическому размеру доказательства21.
-/
noncomputable section
namespace MMRank
open Matrix Module
variable {K I L : Type*} [Field K] [Fintype I]
  [AddCommGroup L] [Module K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- Строки одного трёхмерного ядра служат общей координатной моделью всех срезов. -/
theorem exists_critical_residual_slice_model
    (b : Basis (Fin 5) K L) (w : I → L) (hc : Fintype.card I = 8)
    (A : Fin 5 → I → Matrix (Fin 3) (Fin 3) K)
    (hr : ∀ j i, (A j i).rank ≤ 1)
    (h : ∀ j X, ∑ i, trace (X * A j i) • w i = trace X • b j) :
    finrank K (Fintype.linearCombination K w).ker = 3 ∧
    ∃ μ : I → Fin 3 → K,
      Pairwise (fun i j ↦ LinearIndependent K ![μ i, μ j]) ∧
      Submodule.span K (Set.range μ) = ⊤ ∧
      ∀ j, ∃ Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K,
        (∀ x, Z x 0 0 = 0) ∧
        (∀ i, A j i = A j i 0 0 • 1 + Z (μ i)) ∧
        let M := Submodule.span K (Set.range (A j))
        (1 : Matrix (Fin 3) (Fin 3) K) ∈ M ∧
        3 ≤ finrank K M ∧ finrank K M ≤ 4 ∧
        finrank K M = 1 + finrank K Z.range := by
  classical
  let F := Fintype.linearCombination K w
  let E := Dual K F.ker
  have hf : Function.Surjective F := trace_reconstruction_surjective b F A
    (by intro j X; simpa [F, Fintype.linearCombination_apply] using h j X) 0
  have hd : finrank K L = 5 := by simpa using finrank_eq_card_basis b
  have hk : finrank K F.ker = 3 := by
    have hh := F.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hf, finrank_top, hd, Module.finrank_pi] at hh
    simp only [hc] at hh
    omega
  have hE : finrank K E = 3 := by
    change finrank K (Dual K F.ker) = 3
    rw [Subspace.dual_finrank_eq, hk]
  let e : E ≃ₗ[K] (Fin 3 → K) := (Module.finBasisOfFinrankEq K E hE).equivFun
  let μ₀ (i : I) : E := F.ker.dualRestrict (LinearMap.proj i)
  let μ (i : I) := e (μ₀ i)
  have hp : Pairwise (fun i j ↦ LinearIndependent K ![μ i, μ j]) := by
    intro i j hij
    have hh := trace_reconstruction_kernel_pair_independent b w A hr h (by decide) hij
    have he := hh.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    convert he using 1
    ext a; fin_cases a <;> rfl
  have hs : Submodule.span K (Set.range μ) = ⊤ := by
    have hh := span_dual_kernel_coordinates_eq_top (K := K) F.ker
    change Submodule.span K (Set.range μ₀) = ⊤ at hh
    change Submodule.span K (Set.range (fun i ↦ e (μ₀ i))) = ⊤
    rw [Set.range_comp']
    change Submodule.span K (e.toLinearMap '' Set.range μ₀) = ⊤
    rw [← Submodule.map_span, hh, Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  refine ⟨hk, μ, hp, hs, ?_⟩
  intro j
  obtain ⟨Z₀, hz₀, ha₀⟩ := trace_reconstruction_kernel_rows F (b j) (A j)
    (by intro X; simpa [F, Fintype.linearCombination_apply] using h j X) 0
  let Z := Z₀.comp e.symm.toLinearMap
  have ha (i) : A j i = A j i 0 0 • 1 + Z (μ i) := by
    simpa only [Z, μ, μ₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      e.symm_apply_apply] using ha₀ i
  have hz (x) : Z x 0 0 = 0 := hz₀ _
  let M := Submodule.span K (Set.range (A j))
  have h1 : (1 : Matrix (Fin 3) (Fin 3) K) ∈ M :=
    one_mem_span_of_trace_reconstruction w (b j) (b.ne_zero j) (A j) (h j)
  have he := span_trace_slice_eq_one_sup_range (A j) (fun i ↦ A j i 0 0) μ hs Z ha h1
  have hm : finrank K M = 1 + finrank K Z.range := by
    change finrank K (Submodule.span K (Set.range (A j))) = _
    rw [he]
    exact finrank_one_sup_range_of_diagonal_zero Z 0 hz
  have hlo : 3 ≤ finrank K M := by
    exact card_le_finrank_of_one_mem_rank_one_spanning M
      (span_rank_one_subtype_eq_top_of_spanning_family (A j) (hr j)) h1
  have hu := Z.finrank_range_le
  simp only [Module.finrank_pi, Fintype.card_fin] at hu
  change finrank K (Submodule.span K (Set.range (A j))) = 1 + finrank K Z.range at hm
  exact ⟨Z, hz, ha, h1, hlo, by omega, hm⟩

end MMRank
