module

public import MMRank.RankOneFourSpace
public import MMRank.QuadraticFormCoordinates
public import MMRank.TraceSliceSpace

@[expose] public section

/-! # Четырёхмерный срез выделяет квадратично отделяемый выход
-/
noncomputable section
namespace MMRank
open Matrix Module
variable {K I L : Type*} [Field K] [Fintype I] [AddCommGroup L] [Module K L]

omit [Fintype I] in
/-- Инъективная поправка превращает разные строки ядра в разные простые линии. -/
theorem slice_pair_independent_of_kernel_model
    (A : I → Matrix (Fin 3) (Fin 3) K) (μ : I → Fin 3 → K)
    (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hz : ∀ x, Z x 0 0 = 0) (hi : Function.Injective Z)
    (ha : ∀ i, A i = A i 0 0 • 1 + Z (μ i)) :
    Pairwise fun i j ↦ LinearIndependent K ![A i, A j] := by
  let p : Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K :=
    RankOneFourSpace.centeredMap (Matrix.entryLinearMap K K 0 0)
  have hpi (i) : p (A i) = Z (μ i) := by
    change A i - A i 0 0 • 1 = Z (μ i)
    rw [ha i]
    have hd := hz (μ i)
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      hd, mul_one, add_zero]
    abel
  intro i j hij
  apply LinearIndependent.pair_iff.mpr
  intro s t hst
  have hh := congrArg p hst
  rw [map_add, map_smul, map_smul, map_zero, hpi, hpi] at hh
  have he : Z (s • μ i + t • μ j) = Z 0 := by
    simpa only [map_add, map_smul, map_zero] using hh
  exact LinearIndependent.pair_iff.mp (hp hij) s t (hi he)

/-- При dimM=4 один индекс и его выход отделяются в шести квадратичных координатах. -/
theorem four_dimensional_slice_separated_output
    (w : I → L) (t : L) (A : I → Matrix (Fin 3) (Fin 3) K)
    (hr : ∀ i, (A i).rank ≤ 1) (hcard : 2 ≤ Fintype.card I)
    (h : ∀ χ : Dual K (Matrix (Fin 3) (Fin 3) K),
      ∑ i, χ (A i) • w i = χ 1 • t)
    (μ : I → Fin 3 → K) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hz : ∀ x, Z x 0 0 = 0)
    (ha : ∀ i, A i = A i 0 0 • 1 + Z (μ i))
    (h1 : (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range A))
    (hd : finrank K (Submodule.span K (Set.range A)) = 4)
    (hm : finrank K (Submodule.span K (Set.range A)) = 1 + finrank K Z.range) :
    ∃ i, i ∈ separatedIndices (K := K) (fun i ↦ quadraticVeronese (μ i)) ∧
      t ∈ Submodule.span K {w i} := by
  classical
  let : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hi : Function.Injective Z := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hh := Z.finrank_range_add_finrank_ker
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hh
    omega
  have hpA := slice_pair_independent_of_kernel_model A μ hp Z hz hi ha
  have hn (i) : A i ≠ 0 := by
    obtain ⟨j, hj⟩ := exists_ne i
    simpa using (hpA hj.symm).ne_zero 0
  have hr' (i) : (A i).rank = 1 := by
    have hh : (A i).rank ≠ 0 := by
      intro he
      exact hn i ((matrix_rank_eq_zero_iff _).mp he)
    have := hr i
    omega
  have hproj : Function.Injective (fun i ↦ Submodule.span K ({A i} : Set (Matrix (Fin 3) (Fin 3) K))) := by
    intro i j he
    by_contra hij
    change Submodule.span K {A i} = Submodule.span K {A j} at he
    have hmem : A i ∈ Submodule.span K {A j} := by
      rw [← he]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, hsa⟩ := Submodule.mem_span_singleton.mp hmem
    have hh := LinearIndependent.pair_iff.mp (hpA hij) 1 (-a)
      (by rw [one_smul, neg_smul, hsa, add_neg_cancel])
    exact one_ne_zero hh.1
  obtain ⟨i, χ, Q, hχ1, hχi, hQi, hzero, hscalar⟩ :=
    RankOneFourSpace.exists_linear_quadratic_separator A (by decide) hr' hproj hd.le h1
  obtain ⟨φ, hφ⟩ := exists_quadratic_coordinate_form (Q.comp Z)
  have hQ (k : I) : Q (Z (μ k)) = Q (A k) := by
    rw [ha k]
    exact (hscalar (Z (μ k)) (A k 0 0)).symm.trans
      (congrArg Q (add_comm _ _))
  refine ⟨i, ?_, ?_⟩
  · apply (mem_separatedIndices _ i).mpr
    refine ⟨φ, ?_, ?_⟩
    · simpa only [hφ, QuadraticMap.comp_apply, hQ] using hQi
    · intro j hji
      simpa only [hφ, QuadraticMap.comp_apply, hQ] using (hzero j hji).2
  · have he := h χ
    rw [hχ1, one_smul] at he
    have hs : (∑ k, χ (A k) • w k) = χ (A i) • w i := by
      apply Finset.sum_eq_single i
      · intro k _ hki; rw [(hzero k hki).1, zero_smul]
      · simp
    rw [hs] at he
    rw [← he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end MMRank
