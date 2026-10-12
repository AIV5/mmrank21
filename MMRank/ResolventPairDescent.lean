import MMRank.MixedPairIdentities
import MMRank.OnePairRankDescent

/-! # Операторное выделение одной простой пары

Квадратичное тождество оператора
и одно отношение соседей выделяют полную билинейную пару с явным
операторным первым множителем. Его ранг контролируется рангом сдвига.
-/
namespace MMRank
open Matrix
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

omit [Fintype Q] in
/-- Два корня уничтожающего многочлена дают взвешенную резольвентную
формулу. Она верна в любой конечной матричной размерности. -/
theorem quadratic_resolvent_weighted_identity [DecidableEq P]
    (H : Matrix P P K) (X A : Matrix P Q K) (lam mu c t w : K)
    (hc : c ≠ 0) (ht : t ≠ mu)
    (hpoly : (H - lam • 1) * (H - mu • 1) = 0)
    (hres : (t • 1 - H) * X = (w / c) • A) :
    (c * (t - lam)) • X = w • A + (w / (t - mu)) • ((H - lam • 1) * A) := by
  have hH : (H - lam • 1) * H = mu • (H - lam • 1) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at hpoly
    exact sub_eq_zero.mp hpoly
  have hk : (t - mu) • ((H - lam • 1) * X) =
      (w / c) • ((H - lam • 1) * A) := by
    calc
      _ = (t • (H - lam • 1) - (H - lam • 1) * H) * X := by
        rw [hH]
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_smul, smul_sub]
        abel
      _ = (H - lam • 1) * ((t • 1 - H) * X) := by
        rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
      _ = _ := by rw [hres, Matrix.mul_smul]
  have hk' : c • ((H - lam • 1) * X) =
      (w / (t - mu)) • ((H - lam • 1) * A) := by
    have hh := congrArg (fun Z : Matrix P Q K ↦ (c / (t - mu)) • Z) hk
    simp only [smul_smul] at hh
    have hleft : c / (t - mu) * (t - mu) = c := div_mul_cancel₀ c (sub_ne_zero.mpr ht)
    have hright : c / (t - mu) * (w / c) = w / (t - mu) := by field_simp [hc, sub_ne_zero.mpr ht]
    rwa [hleft, hright] at hh
  have hx : (t - lam) • X = (w / c) • A + (H - lam • 1) * X := by
    rw [← hres]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_smul]
    abel
  rw [← smul_smul, hx, smul_add, smul_smul, hk']
  have hcw : c * (w / c) = w := by field_simp [hc]
  rw [hcw]

/-- Единственное отношение уничтожает общий вклад A и оставляет одну
полную простую пару. Выходная матрица второго фактора остаётся явной. -/
theorem resolvent_pair_diagonal_sum [DecidableEq P]
    (H : Matrix P P K) (A : Matrix P Q K) (X : I → Matrix P Q K)
    (V : I → Matrix Q S K) (lam mu : K) (c t w : I → K)
    (hc : ∀ i, c i ≠ 0)
    (hpoly : (H - lam • 1) * (H - mu • 1) = 0)
    (hres : ∀ i, (t i • 1 - H) * X i = (w i / c i) • A)
    (hw : ∀ i, ¬(t i ≠ lam ∧ t i ≠ mu) → w i = 0)
    (hz : ∑ i, w i • V i = 0) :
    (∑ i : {i | t i ≠ lam ∧ t i ≠ mu}, (c i * (t i - lam)) • matrixCoefficientPair (X i) (V i)) =
      matrixCoefficientPair ((H - lam • 1) * A)
        (∑ i : {i | t i ≠ lam ∧ t i ≠ mu}, (w i / (t i - mu)) • V i) := by
  let J := {i | t i ≠ lam ∧ t i ≠ mu}
  let B := matrixCoefficientPairBilin (K := K) (P := P) (Q := Q) (S := S)
  have he (i : J) : (c i * (t i - lam)) • B (X i) (V i) =
      B A (w i • V i) + B ((H - lam • 1) * A) ((w i / (t i - mu)) • V i) := by
    have hh := congrArg (fun Z : Matrix P Q K ↦ B Z (V i))
      (quadratic_resolvent_weighted_identity H (X i) A lam mu (c i) (t i) (w i)
        (hc i) i.property.2 hpoly (hres i))
    simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] using hh
  have hzJ : ∑ i : J, w i • V i = 0 := by
    have hh : (∑ i, w i • V i) = ∑ i : J, w i • V i :=
      Finset.sum_congr_set J _ _ (fun _ _ ↦ rfl) (fun i hi ↦ by simp [hw i hi])
    exact hh.symm.trans hz
  change (∑ i : J, (c i * (t i - lam)) • B (X i) (V i)) =
    B ((H - lam • 1) * A) (∑ i : J, (w i / (t i - mu)) • V i)
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← map_sum, ← map_sum, hzJ, map_zero, zero_add]

/-- Левое матричное вложение переносит тождество полных пар. Оба
входа остаются независимыми; цикличность следа меняет первый вход. -/
theorem matrixCoefficientPair_sum_left_lift
    {R : Type*} [Fintype R]
    (E : Matrix R P K) (X : I → Matrix P Q K) (V : I → Matrix Q S K)
    (a : I → K) (A : Matrix P Q K) (B : Matrix Q S K)
    (hpair : (∑ i, a i • matrixCoefficientPair (X i) (V i)) = matrixCoefficientPair A B) :
    (∑ i, a i • matrixCoefficientPair (E * X i) (V i)) = matrixCoefficientPair (E * A) B := by
  ext Y Z
  have hh := congrArg (fun f ↦ f (Y * E) Z) hpair
  have ht (U : Matrix P Q K) : trace ((E * U) * Y) = trace (U * (Y * E)) := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    matrixCoefficientPair_apply, ht] using hh

/-- Ненулевой множитель справа уже даёт нужную нижнюю границу ранга;
обратимость резольвентного оператора для этого не требуется. -/
theorem rank_le_of_resolvent_factor [DecidableEq P]
    (H : Matrix P P K) (X A : Matrix P Q K) (t c w : K)
    (hc : c ≠ 0) (hw : w ≠ 0)
    (hres : (t • 1 - H) * X = (w / c) • A) : A.rank ≤ X.rank := by
  have hh := Matrix.rank_mul_le_right (t • 1 - H) X
  rw [hres, Matrix.rank_smul_of_mem_nonZeroDivisors A
    (mem_nonZeroDivisors_of_ne_zero (div_ne_zero hw hc))] at hh
  exact hh

namespace ExactAlgorithm

/-- Первая ранговая минимальность запрещает двумерную правую часть
резольвентного уравнения. Матричная ретракция возвращает операторную
пару в исходный алгоритм; размеры и поле произвольны. -/
theorem IsFirstRankMinimal.resolvent_rank_two_impossible
    {alg : ExactAlgorithm K P Q S I} (hmin : alg.IsFirstRankMinimal)
    (G : Set I) (E : Matrix P (Fin 2) K) (L : Matrix (Fin 2) P K)
    (hLE : L * E = 1) (X : G → Matrix (Fin 2) Q K)
    (hU : ∀ i : G, alg.U i = E * X i)
    (H : Matrix (Fin 2) (Fin 2) K) (A : Matrix (Fin 2) Q K)
    (lam mu : K) (c t w : G → K) (hc : ∀ i, c i ≠ 0) (hw : w ≠ 0)
    (hpoly : (H - lam • 1) * (H - mu • 1) = 0)
    (hres : ∀ i, (t i • 1 - H) * X i = (w i / c i) • A)
    (hz : ∑ i : G, w i • alg.V i = 0) (hA : A.rank = 2)
    (hlam : (lam • 1 - H).rank ≤ 1) (hmu : (mu • 1 - H).rank ≤ 1) : False := by
  have hroot (i : G) (hr : (t i • 1 - H).rank ≤ 1) : w i = 0 := by
    by_contra hwi
    have he := congrArg Matrix.rank (hres i)
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors A
      (mem_nonZeroDivisors_of_ne_zero (div_ne_zero hwi (hc i))), hA] at he
    have hh := Matrix.rank_mul_le_left (t i • 1 - H) (X i)
    rw [he] at hh
    omega
  let J : Set G := {i | t i ≠ lam ∧ t i ≠ mu}
  have hwzero (i : G) (hi : i ∉ J) : w i = 0 := by
    by_cases hl : t i = lam
    · apply hroot i; simpa [hl] using hlam
    · have hm : t i = mu := by by_contra h; exact hi ⟨hl, h⟩
      apply hroot i; simpa [hm] using hmu
  obtain ⟨j, hj⟩ : ∃ j : G, w j ≠ 0 := by simpa [funext_iff] using hw
  have hjJ : j ∈ J := by by_contra h; exact hj (hwzero j h)
  have hpair := resolvent_pair_diagonal_sum H A X (fun i : G ↦ alg.V i)
    lam mu c t w hc hpoly hres hwzero hz
  have hfull := matrixCoefficientPair_sum_left_lift E
    (fun i : J ↦ X i) (fun i : J ↦ alg.V i) (fun i : J ↦ c i * (t i - lam))
    ((H - lam • 1) * A) (∑ i : J, (w i / (t i - mu)) • alg.V i) hpair
  let a : G → K := fun i ↦ if i ∈ J then c i * (t i - lam) else 0
  have heq : (∑ i : G, a i • matrixCoefficientPair (E * X i) (alg.V i)) =
      ∑ i : J, (c i * (t i - lam)) • matrixCoefficientPair (E * X i) (alg.V i) :=
    Finset.sum_congr_set J _ _ (fun i hi ↦ by simp [a, hi]) (fun i hi ↦ by simp [a, hi])
  have hp : (∑ i : G, a i • matrixCoefficientPair (alg.U i) (alg.V i)) =
      matrixCoefficientPair (E * ((H - lam • 1) * A))
        (∑ i : J, (w i / (t i - mu)) • alg.V i) := by
    simpa only [hU] using heq.trans hfull
  have ha : a j ≠ 0 := by
    simp only [a, ite_eq_left hjJ]
    exact mul_ne_zero (hc j) (sub_ne_zero.mpr hjJ.1)
  have hle := hmin.rank_le_of_pair_sum G a j (E * ((H - lam • 1) * A))
    (∑ i : J, (w i / (t i - mu)) • alg.V i) ha hp
  have hX : X j = L * alg.U j := by rw [hU j, ← Matrix.mul_assoc, hLE, Matrix.one_mul]
  have hrank := rank_le_of_resolvent_factor H (X j) A (t j) (c j) (w j) (hc j) hj (hres j)
  rw [hA, hX] at hrank
  have hlow := hrank.trans (Matrix.rank_mul_le_right L (alg.U j))
  have hneg : (-1 : K) • (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) = H - lam • 1 := by
    simp only [neg_smul, one_smul, neg_sub]
  have hr : (H - lam • 1).rank ≤ 1 := by
    rw [← hneg, Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr one_ne_zero))]
    exact hlam
  have hsmall := (Matrix.rank_mul_le_right E ((H - lam • 1) * A)).trans
    ((Matrix.rank_mul_le_left (H - lam • 1) A).trans hr)
  omega

end ExactAlgorithm

end MMRank
