module

public import MMRank.SupportedTestSpan
public import MMRank.RankFactorization
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section

/-! # Базис и двойственные следовые формы на минимальном носителе -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Минимальный носитель простого теста даёт базис средних направлений Uᵢ. -/
theorem exists_basis_of_minimal_gamma_support (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (hc : G.ncard = Fintype.card Q) :
    ∃ b : Basis G K (Q → K), ∀ i : G, alg.U i.val = vecMulVec p (b i) := by
  classical
  have he := alg.span_eq_fixedColumnSpace_of_minimal_gamma_support G p hp s hs hG hc
  have hm (i : G) : alg.U i.val ∈ fixedColumnSpace (Q := Q) p := by
    rw [← he]
    exact Submodule.subset_span ⟨i.val, i.property, rfl⟩
  choose q hq using hm
  let f := (vecMulVecBilin K K p : (Q → K) →ₗ[K] Matrix P Q K)
  have hspan : Submodule.span K (Set.range q) = ⊤ := by
    apply Submodule.map_injective_of_injective (fixedColumnMap_injective hp)
    change (Submodule.span K (Set.range q)).map f = (⊤ : Submodule K (Q → K)).map f
    rw [Submodule.map_span, Submodule.map_top]
    have hr : f '' Set.range q = alg.U '' G := by
      ext A
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.val, i.property, (hq i).symm⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨q ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, hq ⟨i, hi⟩⟩
    rw [hr, he]
    rfl
  let b := basisOfTopLeSpanOfCardEqFinrank q hspan.ge
    (by simpa only [Set.fintypeCard_eq_ncard, Module.finrank_fintype_fun_eq_card] using hc)
  refine ⟨b, fun i ↦ ?_⟩
  simpa [b] using (hq i).symm

/-- Координаты базиса читают взвешенные соседние следовые формы.
Это точное равенство функционалов, не только утверждение об их рангах. -/
theorem trace_coordinates_of_test_basis (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (b : Basis G K (Q → K)) (hb : ∀ i : G, alg.U i.val = vecMulVec p (b i))
    (B : Matrix S Q K) (i : G) :
    b.repr (s ᵥ* B) i = alg.toCoefficients.gamma (vecMulVec p s) i.val *
      alg.toCoefficients.beta B i.val := by
  classical
  have he := alg.rotate.exact_formula B (vecMulVec p s)
  change vecMulVec p s * B = ∑ j, (alg.toCoefficients.beta B j *
    alg.toCoefficients.gamma (vecMulVec p s) j) • alg.U j at he
  have hsum : (∑ j, (alg.toCoefficients.beta B j * alg.toCoefficients.gamma (vecMulVec p s) j) • alg.U j) =
      ∑ j : G, (alg.toCoefficients.beta B j.val * alg.toCoefficients.gamma (vecMulVec p s) j.val) • alg.U j.val := by
    exact Finset.sum_congr_set G _ _ (fun _ _ ↦ rfl) (fun j hj ↦ by simp [hG j hj])
  rw [hsum, vecMulVec_mul] at he
  have hv : s ᵥ* B = ∑ j : G,
      (alg.toCoefficients.beta B j.val * alg.toCoefficients.gamma (vecMulVec p s) j.val) • b j := by
    apply fixedColumnMap_injective hp
    change vecMulVec p (s ᵥ* B) = (vecMulVecBilin K K p) _
    rw [map_sum]
    simp only [map_smul]
    change vecMulVec p (s ᵥ* B) = ∑ j : G,
      (alg.toCoefficients.beta B j.val * alg.toCoefficients.gamma (vecMulVec p s) j.val) •
        vecMulVec p (b j)
    simpa only [hb] using he
  rw [hv, b.repr_sum_self]
  exact mul_comm _ _

/-- Ни один вес простого теста не исчезает на его базисном носителе. -/
theorem gamma_ne_zero_of_test_basis (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (b : Basis G K (Q → K)) (hb : ∀ i : G, alg.U i.val = vecMulVec p (b i))
    (i : G) : alg.toCoefficients.gamma (vecMulVec p s) i.val ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := exists_vecMul_eq s hs (b i)
  have hh := alg.trace_coordinates_of_test_basis G p hp s hG b hb B i
  simp only [hB, b.repr_self, Finsupp.single_eq_same] at hh
  intro hz
  simp [hz] at hh

/-- Взвешенные Vᵢ — внешние произведения двойственных координат базиса
и общего s. Равенство действует без деления на вес. -/
theorem weighted_V_of_test_basis [DecidableEq Q] (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (b : Basis G K (Q → K)) (hb : ∀ i : G, alg.U i.val = vecMulVec p (b i))
    (i : G) :
    alg.toCoefficients.gamma (vecMulVec p s) i.val • alg.V i.val =
      vecMulVec (fun q ↦ b.repr (Pi.single q 1) i) s := by
  classical
  ext q k
  have hh := alg.trace_coordinates_of_test_basis G p hp s hG b hb (Matrix.single k q 1) i
  have hv : s ᵥ* Matrix.single k q (1 : K) = s k • Pi.single q 1 := by
    ext j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.single, ite_and, eq_comm]
  rw [hv, map_smul] at hh
  simpa [Coefficients.beta, traceCoordinates, trace_mul_single, vecMulVec, mul_comm] using hh.symm

/-- Точные перекрёстные произведения соседних коэффициентов: двойственность
средних базисов, в порядке правого действия UⱼVᵢ. -/
theorem weighted_UV_of_test_basis [DecidableEq ι] (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (b : Basis G K (Q → K)) (hb : ∀ i : G, alg.U i.val = vecMulVec p (b i))
    (i j : G) :
    alg.toCoefficients.gamma (vecMulVec p s) i.val • (alg.U j.val * alg.V i.val) =
      (if j = i then (1 : K) else 0) • vecMulVec p s := by
  classical
  rw [← Matrix.mul_smul, alg.weighted_V_of_test_basis G p hp s hG b hb i, hb j,
    vecMulVec_mul_vecMulVec]
  have hd : b j ⬝ᵥ (fun q ↦ b.repr (Pi.single q 1) i) = b.repr (b j) i := by
    have hsingle (q : Q) : (fun x : Q ↦ if q = x then (1 : K) else 0) = Pi.single q 1 := by
      ext x; simp [Pi.single_apply, eq_comm]
    simpa only [Basis.coord_apply, dotProduct, hsingle, smul_eq_mul] using
      ((b.coord i).pi_apply_eq_sum_univ (b j)).symm
  rw [hd, b.repr_self_apply]
  ext a c
  simp [vecMulVec, mul_left_comm]

/-- При ненулевом простом тесте каждый соседний Vᵢ имеет ранг ровно один. -/
theorem V_rank_eq_one_of_test_basis (alg : ExactAlgorithm K P Q S ι)
    (G : Set ι) (p : P → K) (hp : p ≠ 0) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (b : Basis G K (Q → K)) (hb : ∀ i : G, alg.U i.val = vecMulVec p (b i))
    (i : G) : (alg.V i.val).rank = 1 := by
  classical
  have hw := alg.gamma_ne_zero_of_test_basis G p hp s hs hG b hb i
  have he := alg.weighted_V_of_test_basis G p hp s hG b hb i
  have hr := rank_vecMulVec_le (fun q ↦ b.repr (Pi.single q 1) i) s
  rw [← he, rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hw)] at hr
  have hv : alg.V i.val ≠ 0 := by
    intro hz
    have hh := alg.weighted_UV_of_test_basis G p hp s hG b hb i i
    have hC : vecMulVec p s ≠ 0 := by
      obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by simpa [funext_iff] using hp
      obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by simpa [funext_iff] using hs
      intro hzero
      exact (mul_ne_zero hj hk) (congrFun (congrFun hzero j) k)
    exact hC (by simpa [hz] using hh.symm)
  have hr0 : (alg.V i.val).rank ≠ 0 := mt (matrix_rank_eq_zero_iff _).mp hv
  omega

end MMRank.ExactAlgorithm
