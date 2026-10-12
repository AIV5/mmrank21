import MMRank.LinearRankSum
import MMRank.RankOneHyperplanes
import MMRank.TraceDuality

/-! # Коэффициентный код и естественные строки ядра реконструкции
-/

noncomputable section
namespace MMRank
open Matrix Module
variable {K L I J Q : Type*} [Field K] [AddCommGroup L] [Module K L]
  [Fintype I] [Fintype Q]

omit [Fintype I] in
/-- Одна диагональная координата реконструирует тест в выходе F. -/
theorem trace_reconstruction_diagonal
    (F : (I → K) →ₗ[K] L) (t : L) (A : I → Matrix Q Q K)
    (h : ∀ X, F (fun i ↦ trace (X * A i)) = trace X • t) (q₀ : Q) :
    F (fun i ↦ A i q₀ q₀) = t := by
  classical
  simpa only [trace_single_mul, trace_single_eq_same, one_smul]
    using h (Matrix.single q₀ q₀ 1)

omit [Fintype I] in
/-- Координатная реконструкция, без секции F и без матричного фактора. -/
theorem trace_reconstruction_kernel_rows [DecidableEq Q]
    (F : (I → K) →ₗ[K] L) (t : L) (A : I → Matrix Q Q K)
    (h : ∀ X, F (fun i ↦ trace (X * A i)) = trace X • t) (q₀ : Q) :
    ∃ Z : Dual K F.ker →ₗ[K] Matrix Q Q K,
      (∀ μ, Z μ q₀ q₀ = 0) ∧
      ∀ i, A i = A i q₀ q₀ • 1 + Z (F.ker.dualRestrict (LinearMap.proj i)) := by
  classical
  have hc := trace_reconstruction_diagonal F t A h q₀
  have hab (a b : Q) : F (fun i ↦ A i a b) = (1 : Matrix Q Q K) a b • t := by
    by_cases hab : a = b
    · subst b
      simpa [trace_single_mul] using h (Matrix.single a a 1)
    · simpa [trace_single_mul, trace_single_eq_of_ne b a (1 : K) (Ne.symm hab),
        Matrix.one_apply, hab]
        using h (Matrix.single b a 1)
  let δ (a b : Q) : F.ker := ⟨fun i ↦ A i a b - (1 : Matrix Q Q K) a b * A i q₀ q₀,
    by
      change F ((fun i ↦ A i a b) - (1 : Matrix Q Q K) a b • (fun i ↦ A i q₀ q₀)) = 0
      rw [map_sub, map_smul, hab, hc, sub_self]⟩
  let Z : Dual K F.ker →ₗ[K] Matrix Q Q K :=
    { toFun μ := fun a b ↦ μ (δ a b)
      map_add' := by intros; ext a b; rfl
      map_smul' := by intros; ext a b; rfl }
  refine ⟨Z, ?_, ?_⟩
  · intro μ
    have hz : δ q₀ q₀ = 0 := by ext i; simp [δ]
    change μ (δ q₀ q₀) = 0
    rw [hz, map_zero]
  · intro i
    ext a b
    change A i a b = A i q₀ q₀ * (1 : Matrix Q Q K) a b +
      (A i a b - (1 : Matrix Q Q K) a b * A i q₀ q₀)
    ring

omit [Fintype I] in
/-- Базис тестов даёт сюръективный выход F. -/
theorem trace_reconstruction_surjective [Fintype J]
    (b : Basis J K L) (F : (I → K) →ₗ[K] L)
    (A : J → I → Matrix Q Q K)
    (h : ∀ j X, F (fun i ↦ trace (X * A j i)) = trace X • b j) (q₀ : Q) :
    Function.Surjective F := by
  rw [← LinearMap.range_eq_top]
  apply top_le_iff.mp
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact ⟨_, trace_reconstruction_diagonal F (b j) (A j) (h j) q₀⟩

/-- Следовая реконструкция допускает любой выходной функционал. -/
theorem trace_reconstruction_dual_identity [DecidableEq Q]
    (w : I → L) (t : L) (A : I → Matrix Q Q K)
    (h : ∀ X, ∑ i, trace (X * A i) • w i = trace X • t) (φ : Dual K L) :
    ∑ i, φ (w i) • A i = φ t • (1 : Matrix Q Q K) := by
  classical
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  have hh := congrArg φ (h X)
  simp only [map_sum, map_smul, smul_eq_mul] at hh
  simpa only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
    smul_eq_mul, Matrix.mul_one, mul_comm] using hh

/-- На матричной стороне следовые тесты эквивалентны всем линейным формам. -/
theorem trace_reconstruction_linear_forms [DecidableEq Q]
    (w : I → L) (t : L) (A : I → Matrix Q Q K)
    (h : ∀ X, ∑ i, trace (X * A i) • w i = trace X • t)
    (χ : Dual K (Matrix Q Q K)) :
    ∑ i, χ (A i) • w i = χ 1 • t := by
  classical
  obtain ⟨X, hX, _⟩ := exists_unique_trace_representation χ
  simpa only [hX, trace_mul_comm (A _) X, Matrix.one_mul] using h X

/-- Ненулевой тест требует единицу в оболочке его срезов. -/
theorem one_mem_span_of_trace_reconstruction [DecidableEq Q]
    (w : I → L) (t : L) (ht : t ≠ 0) (A : I → Matrix Q Q K)
    (h : ∀ X, ∑ i, trace (X * A i) • w i = trace X • t) :
    (1 : Matrix Q Q K) ∈ Submodule.span K (Set.range A) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K ht
  have hh := trace_reconstruction_dual_identity w t A h φ
  rw [hφ, one_smul] at hh
  rw [← hh]
  exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i)))

/-- Свёртка любого ненулевого выходного функционала требует q активных индексов. -/
theorem trace_reconstruction_support_bound [Fintype J] [DecidableEq Q]
    (b : Basis J K L) (w : I → L) (A : J → I → Matrix Q Q K)
    (hA : ∀ j i, (A j i).rank ≤ 1)
    (h : ∀ j X, ∑ i, trace (X * A j i) • w i = trace X • b j)
    (φ : Dual K L) (hφ : φ ≠ 0) :
    Fintype.card Q ≤ {i | φ (w i) ≠ 0}.ncard := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, φ (b j) ≠ 0 := by
    by_contra hn
    apply hφ
    apply b.ext
    intro j
    simpa using not_exists.mp hn j
  have hm := trace_reconstruction_dual_identity w (b j) (A j) (h j) φ
  have hr := matrix_rank_weighted_sum_le (A j) (fun i ↦ φ (w i)) 1 (hA j)
  rw [hm, rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hj),
    Matrix.rank_one, mul_one] at hr
  exact hr

/-- Отношение строк ядра есть коэффициентное слово выходного кода. -/
theorem trace_reconstruction_kernel_relation_bound [Fintype J] [DecidableEq Q]
    (b : Basis J K L) (w : I → L) (A : J → I → Matrix Q Q K)
    (hA : ∀ j i, (A j i).rank ≤ 1)
    (h : ∀ j X, ∑ i, trace (X * A j i) • w i = trace X • b j)
    (c : I → K) (hc : c ≠ 0)
    (hrel : ∑ i, c i • (Fintype.linearCombination K w).ker.dualRestrict
      (LinearMap.proj i) = 0) :
    Fintype.card Q ≤ {i | c i ≠ 0}.ncard := by
  classical
  let F := Fintype.linearCombination K w
  let ψ : Dual K (I → K) := ∑ i, c i • LinearMap.proj i
  have hψ : ψ ∈ F.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    have hh := congrArg (fun μ : Dual K F.ker ↦ μ ⟨z, hz⟩) hrel
    simpa only [ψ, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.dualRestrict_apply, LinearMap.proj_apply, LinearMap.zero_apply] using hh
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hψ
  obtain ⟨φ, hφ⟩ := hψ
  have he (i : I) : φ (w i) = c i := by
    have hh := congrArg (fun f : Dual K (I → K) ↦ f (Pi.single i 1)) hφ
    simpa [ψ, F, Pi.single_apply, mul_ite] using hh
  have hφ0 : φ ≠ 0 := by
    intro hz
    apply hc
    ext i
    rw [← he, hz]
    rfl
  simpa only [he] using trace_reconstruction_support_bound b w A hA h φ hφ0

/-- При среднем размере≥3 строки ядра попарно независимы. -/
theorem trace_reconstruction_kernel_pair_independent [Fintype J] [DecidableEq Q]
    (b : Basis J K L) (w : I → L) (A : J → I → Matrix Q Q K)
    (hA : ∀ j i, (A j i).rank ≤ 1)
    (h : ∀ j X, ∑ k, trace (X * A j k) • w k = trace X • b j)
    (hq : 3 ≤ Fintype.card Q) {i j : I} (hij : i ≠ j) :
    LinearIndependent K ![(Fintype.linearCombination K w).ker.dualRestrict (LinearMap.proj i),
      (Fintype.linearCombination K w).ker.dualRestrict (LinearMap.proj j)] := by
  classical
  apply LinearIndependent.pair_iff.mpr
  intro s t hst
  let c : I → K := Pi.single i s + Pi.single j t
  have hr : ∑ k, c k • (Fintype.linearCombination K w).ker.dualRestrict
      (LinearMap.proj k) = 0 := by
    simpa [c, add_smul, Finset.sum_add_distrib, Pi.single_apply] using hst
  have hs : {k | c k ≠ 0} ⊆ ({i, j} : Set I) := by
    intro k hk
    by_contra hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
    simp [c, Pi.single_apply, hn.1, hn.2] at hk
  have hc : c = 0 := by
    by_contra hn
    have hb := trace_reconstruction_kernel_relation_bound b w A hA h c hn hr
    have hb2 : {k | c k ≠ 0}.ncard ≤ 2 := by
      simpa only [Set.ncard_pair hij] using Set.ncard_le_ncard hs (Set.toFinite _)
    omega
  have hi := congrFun hc i
  have hj := congrFun hc j
  exact ⟨by simpa [c, Pi.single_apply, hij] using hi,
    by simpa [c, Pi.single_apply, Ne.symm hij] using hj⟩

/-- Ограничения координат порождают двойственное пространство любого подпространства. -/
theorem span_dual_kernel_coordinates_eq_top (H : Submodule K (I → K)) :
    Submodule.span K (Set.range (fun i ↦ H.dualRestrict (LinearMap.proj i))) = ⊤ := by
  classical
  have he (i : I) : (Pi.basisFun K I).dualBasis i = LinearMap.proj i := by
    ext x
    simp
  have hs : Submodule.span K (Set.range (fun i : I ↦ (LinearMap.proj i : Dual K (I → K)))) = ⊤ := by
    rw [show (fun i : I ↦ (LinearMap.proj i : Dual K (I → K))) =
      (Pi.basisFun K I).dualBasis from funext (fun i ↦ (he i).symm)]
    exact (Pi.basisFun K I).dualBasis.span_eq
  rw [Set.range_comp', ← Submodule.map_span, hs, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Subspace.dualRestrict_surjective (W := H))

end MMRank
