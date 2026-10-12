module

public import MMRank.LocalPairReplacement
public import MMRank.RankSumMinimality

@[expose] public section

/-! # Один низкоранговый обмен полной билинейной пары

Ненулевой коэффициент разложения простой
пары разрешает заменить один первый множитель. Второй и выходной
столбцы не входят в минимизируемый потенциал.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Скалярное тождество одного обмена; ни матрицы, ни независимость
старых коэффициентов не нужны. -/
theorem scalar_pair_pivot_identity
    (r t c : I → K) (j : I) (s : K) (hc : c j ≠ 0)
    (hs : (∑ i, c i * r i) = s) :
    (∑ i, (if i = j then s else r i) *
      (if i = j then (c j)⁻¹ * t j else t i - c i / c j * t j)) = ∑ i, r i * t i := by
  classical
  have hi (i : I) : (if i = j then s else r i) *
      (if i = j then (c j)⁻¹ * t j else t i - c i / c j * t j) =
      r i * t i + ((if i = j then s else 0) - c i * r i) / c j * t j := by
    by_cases hij : i = j
    · subst i
      simp [div_eq_mul_inv]
      field_simp [hc]
      ring
    · simp only [ite_eq_right hij]; ring
  simp_rw [hi, div_eq_mul_inv]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    Finset.sum_sub_distrib]
  simp [hs]

/-- Простую пару из оболочки можно поставить на любой индекс с ненулевым
коэффициентом её разложения, сохранив остальные первые множители. -/
theorem exists_one_pair_exchange
    (alg : ExactAlgorithm K P Q S I) (G : Set I) (c : G → K) (j : G)
    (A : Matrix P Q K) (B : Matrix Q S K) (hc : c j ≠ 0)
    (h : (∑ i : G, c i • matrixCoefficientPair (alg.U i) (alg.V i)) =
      matrixCoefficientPair A B) :
    ∃ e : ExactAlgorithm K P Q S I,
      e.U j = A ∧ ∀ i, i ≠ j.val → e.U i = alg.U i := by
  classical
  let d : I → K := fun i ↦ if hi : i ∈ G then c ⟨i, hi⟩ else 0
  let U := Function.update alg.U j.val A
  let V := Function.update alg.V j.val B
  let W : I → Matrix S P K := fun i ↦ if i = j.val then (c j)⁻¹ • alg.W j
    else alg.W i - (d i / c j) • alg.W j
  have hd : d j = c j := by simp [d, j.property]
  have hex : (Coefficients.mk U V W).TraceIdentity := by
    intro X Y Z
    let r := fun i ↦ trace (alg.U i * X) * trace (alg.V i * Y)
    let t := fun i ↦ trace (alg.W i * Z)
    let s := trace (A * X) * trace (B * Y)
    have hs : (∑ i, d i * r i) = s := by
      have he := congrArg (fun f ↦ f X Y) h
      have he' : (∑ i : G, c i * r i) = s := by
        simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
          matrixCoefficientPair_apply] using he
      have hs' : (∑ i, d i * r i) = ∑ i : G, c i * r i :=
        Finset.sum_congr_set G _ _ (fun i hi ↦ by simp [d, hi])
          (fun i hi ↦ by simp [d, hi])
      exact hs'.trans he'
    have hr (i) : trace (U i * X) * trace (V i * Y) = if i = j.val then s else r i := by
      by_cases hi : i = j.val <;> simp [U, V, hi, r, s]
    have ht (i) : trace (W i * Z) = if i = j.val then (d j)⁻¹ * t j
        else t i - d i / d j * t j := by
      by_cases hi : i = j.val <;>
        simp [W, hi, hd, Matrix.sub_mul, Matrix.smul_mul, trace_sub, trace_smul, t]
    rw [alg.trace_identity]
    change (∑ i, r i * t i) = ∑ i, (trace (U i * X) * trace (V i * Y)) * trace (W i * Z)
    simp_rw [hr, ht]
    exact (scalar_pair_pivot_identity r t d j s (by simpa [hd] using hc) hs).symm
  refine ⟨⟨⟨U, V, W⟩, (Coefficients.isExact_iff_traceIdentity _).mpr hex⟩, ?_, ?_⟩
  · change U j = A; simp [U]
  · intro i hi; change U i = alg.U i; simp [U, hi]

/-- Минимальность первой ранговой суммы согласует каждое ненулевое
коэффициентное место простой пары с рангом её первого фактора. -/
theorem IsFirstRankMinimal.rank_le_of_pair_sum
    {alg : ExactAlgorithm K P Q S I} (hmin : alg.IsFirstRankMinimal)
    (G : Set I) (c : G → K) (j : G)
    (A : Matrix P Q K) (B : Matrix Q S K) (hc : c j ≠ 0)
    (h : (∑ i : G, c i • matrixCoefficientPair (alg.U i) (alg.V i)) =
      matrixCoefficientPair A B) : (alg.U j).rank ≤ A.rank := by
  obtain ⟨e, hj, he⟩ := alg.exists_one_pair_exchange G c j A B hc h
  by_contra! hlt
  have hsum : (∑ i, (e.U i).rank) < ∑ i, (alg.U i).rank := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = j.val
      · subst i; rw [hj]; omega
      · rw [he i hi]
    · exact ⟨j.val, Finset.mem_univ _, by rw [hj]; exact hlt⟩
  exact (not_lt_of_ge (hmin e)) hsum

end MMRank.ExactAlgorithm
