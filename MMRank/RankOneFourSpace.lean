module

public import MMRank.RankOneMatrixSpaces
public import MMRank.LinearRankSum
public import MMRank.ConnectivityCost
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

/-! # Локальный разделитель в четырёхмерном rank1-пространстве

Квадратичная часть строится из линейной:
минор матрицы `T - χ(T) I`. Конструкция не делит на2 и сохраняется при
добавлении скалярной единицы. Матрицы действуют на строки справа;
в этом модуле используются только записи, ранги и внешние произведения.
-/
noncomputable section
namespace MMRank.RankOneFourSpace
open Matrix Module
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Удаление скалярной компоненты, измеряемой χ. -/
def centeredMap (χ : Matrix n n K →ₗ[K] K) :
    Matrix n n K →ₗ[K] Matrix n n K :=
  LinearMap.id - χ.smulRight 1

omit [Fintype n] in
@[simp] theorem centeredMap_apply (χ : Matrix n n K →ₗ[K] K) (T : Matrix n n K) :
    centeredMap χ T = T - χ T • 1 := rfl

/-- Произвольный двумерный минор центрированной матрицы как квадратичная форма. -/
def shiftedMinor (χ : Matrix n n K →ₗ[K] K) (i j k l : n) :
    QuadraticForm K (Matrix n n K) :=
  QuadraticMap.linMulLin ((Matrix.entryLinearMap K K i k).comp (centeredMap χ))
    ((Matrix.entryLinearMap K K j l).comp (centeredMap χ)) -
  QuadraticMap.linMulLin ((Matrix.entryLinearMap K K i l).comp (centeredMap χ))
    ((Matrix.entryLinearMap K K j k).comp (centeredMap χ))

omit [Fintype n] in
@[simp] theorem shiftedMinor_apply (χ : Matrix n n K →ₗ[K] K)
    (i j k l : n) (T : Matrix n n K) :
    shiftedMinor χ i j k l T =
      (centeredMap χ T) i k * (centeredMap χ T) j l -
      (centeredMap χ T) i l * (centeredMap χ T) j k := rfl

omit [Fintype n] in
theorem shiftedMinor_add_scalar (χ : Matrix n n K →ₗ[K] K) (hχ : χ 1 = 1)
    (i j k l : n) (T : Matrix n n K) (c : K) :
    shiftedMinor χ i j k l (T + c • 1) = shiftedMinor χ i j k l T := by
  have hc : centeredMap χ 1 = 0 := by simp [hχ]
  simp only [shiftedMinor_apply, map_add, map_smul, hc, smul_zero, add_zero]

theorem shiftedMinor_zero_of_rank_le_one (χ : Matrix n n K →ₗ[K] K)
    (i j k l : n) (T : Matrix n n K) (hT : T.rank ≤ 1) (hχ : χ T = 0) :
    shiftedMinor χ i j k l T = 0 := by
  simpa [hχ] using minor_two_eq_zero_of_rank_le_one T hT i j k l

omit [DecidableEq n] in
/-- Ранг больше1 обнаруживается одним двумерным минором, над любым полем. -/
theorem exists_minor_two_ne_zero (T : Matrix n n K) (hT : 1 < T.rank) :
    ∃ i j k l, T i k * T j l - T i l * T j k ≠ 0 := by
  by_contra! h
  obtain ⟨x, y, hxy⟩ := (exists_outerProduct_iff_minors_eq_zero T).mpr
    (fun i j k l ↦ sub_eq_zero.mp (h i j k l))
  have he : T = vecMulVec x y := by ext i j; exact hxy i j
  have hr := rank_vecMulVec_le (R := K) x y
  rw [← he] at hr
  omega

/-- Вычитание ненулевой скалярной единицы из rank1-матрицы оставляет ранг≥2. -/
theorem one_lt_rank_sub_scalar (hsize : 3 ≤ Fintype.card n)
    (T : Matrix n n K) (hT : T.rank ≤ 1) (c : K) (hc : c ≠ 0) :
    1 < (T - c • 1).rank := by
  let D := T - c • (1 : Matrix n n K)
  have hh := matrix_rank_sum_le (fun i : Fin 2 ↦ ![T, -D] i)
  have he : T + -D = c • (1 : Matrix n n K) := by dsimp [D]; abel
  have hn : (-D).rank = D.rank := by
    rw [← neg_one_smul K D]
    exact rank_smul_of_mem_nonZeroDivisors D (mem_nonZeroDivisors_of_ne_zero (by simp))
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
  rw [he, rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc),
    rank_one, hn] at hh
  dsimp [D] at hh
  omega

/-- Любой нормированный линейный разделитель автоматически даёт инвариантный
квадратичный разделитель в виде разности двух произведений линейных форм. -/
theorem exists_quadratic_separator_of_linear {I : Type*}
    (hsize : 3 ≤ Fintype.card n) (A : I → Matrix n n K) (j : I)
    (χ : Matrix n n K →ₗ[K] K) (hχI : χ 1 = 1) (hχj : χ (A j) ≠ 0)
    (hr : ∀ i, (A i).rank ≤ 1) (hzero : ∀ i, i ≠ j → χ (A i) = 0) :
    ∃ Q : QuadraticForm K (Matrix n n K),
      Q (A j) ≠ 0 ∧ (∀ i, i ≠ j → Q (A i) = 0) ∧
      (∀ (T : Matrix n n K) (c : K), Q (T + c • 1) = Q T) := by
  obtain ⟨a, b, c, d, habcd⟩ := exists_minor_two_ne_zero (centeredMap χ (A j))
    (one_lt_rank_sub_scalar hsize (A j) (hr j) (χ (A j)) hχj)
  refine ⟨shiftedMinor χ a b c d, habcd, ?_, ?_⟩
  · intro i hi
    exact shiftedMinor_zero_of_rank_le_one χ a b c d (A i) (hr i) (hzero i hi)
  · intro T t
    exact shiftedMinor_add_scalar χ hχI a b c d T t

end MMRank.RankOneFourSpace

namespace MMRank.RankOneFourSpace
open Matrix Module
open scoped TensorProduct
variable {K I V : Type*} [Field K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Пространство всех значений линейных форм на данном семействе. -/
def familyWords (A : I → V) : Submodule K (I → K) :=
  (LinearMap.pi fun i ↦ (Module.Dual.eval K V) (A i)).range

/-- Двойственные координатные оценки воспроизводят исходные векторы. -/
def familyEmbedding (A : I → V) : Module.Dual K (familyWords (K := K) A) →ₗ[K] V :=
  (Module.evalEquiv K V).symm.toLinearMap.comp
    (LinearMap.pi (fun i ↦ (Module.Dual.eval K V) (A i))).rangeRestrict.dualMap

omit [Fintype I] in
theorem familyEmbedding_injective (A : I → V) :
    Function.Injective (familyEmbedding (K := K) A) :=
  (Module.evalEquiv K V).symm.injective.comp
    (LinearMap.dualMap_injective_of_surjective
      (LinearMap.pi (fun i ↦ (Module.Dual.eval K V) (A i))).surjective_rangeRestrict)

omit [Fintype I] in
@[simp] theorem familyEmbedding_coordinateEval (A : I → V) (i : I) :
    familyEmbedding (K := K) A (coordinateEval (familyWords (K := K) A) i) = A i := by
  apply (Module.evalEquiv K V).injective
  change (Module.evalEquiv K V) ((Module.evalEquiv K V).symm
    ((LinearMap.pi (fun i ↦ (Module.Dual.eval K V) (A i))).rangeRestrict.dualMap
      (coordinateEval (familyWords (K := K) A) i))) = (Module.evalEquiv K V) (A i)
  rw [LinearEquiv.apply_symm_apply]
  ext φ
  rfl

omit [Fintype I] in
theorem familyEmbedding_map_span (A : I → V) (s : Set I) :
    (coordinateEvalSpan (familyWords (K := K) A) s).map (familyEmbedding (K := K) A) =
      Submodule.span K (A '' s) := by
  simp only [coordinateEvalSpan, Submodule.map_span, Set.image_image,
    familyEmbedding_coordinateEval]

theorem familyWords_finrank (A : I → V) :
    finrank K (familyWords (K := K) A) = finrank K (Submodule.span K (Set.range A)) := by
  have hh := familyEmbedding_map_span (K := K) A Set.univ
  rw [coordinateEvalSpan_univ, Submodule.map_top, Set.image_univ] at hh
  rw [← hh, LinearMap.finrank_range_of_inj (familyEmbedding_injective (K := K) A),
    Subspace.dual_finrank_eq]

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype I] in
/-- Образ матрицы из rank1-оболочки лежит в оболочке её первых факторов. -/
theorem rank_le_factor_span (x : I → m → K) (y : I → n → K) (s : Set I)
    (T : Matrix m n K) (hT : T ∈ Submodule.span K ((fun i ↦ vecMulVec (x i) (y i)) '' s)) :
    T.rank ≤ finrank K (Submodule.span K (x '' s)) := by
  apply Submodule.finrank_mono
  rintro _ ⟨u, rfl⟩
  induction hT using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      change vecMulVec (x i) (y i) *ᵥ u ∈ Submodule.span K (x '' s)
      rw [vecMulVec_mulVec, op_smul_eq_smul]
      exact (Submodule.span K (x '' s)).smul_mem (y i ⬝ᵥ u)
        (Submodule.subset_span ⟨i, hi, rfl⟩)
  | zero => simp
  | add A B _ _ hA hB => simpa using (Submodule.span K (x '' s)).add_mem hA hB
  | smul c A _ hA => simpa using (Submodule.span K (x '' s)).smul_mem c hA

/-- Связный блок rank1-матриц оплачивает удвоенный ранг любого своего элемента. -/
theorem twice_rank_le_span_add_one (x : I → m → K) (y : I → n → K)
    (s : Set I) (hconn : SpanConnected K (fun i ↦ vecMulVec (x i) (y i)) s)
    (hn : ∀ i ∈ s, vecMulVec (x i) (y i) ≠ 0)
    (T : Matrix m n K) (hT : T ∈ Submodule.span K ((fun i ↦ vecMulVec (x i) (y i)) '' s)) :
    2 * T.rank ≤
      finrank K (Submodule.span K ((fun i ↦ vecMulVec (x i) (y i)) '' s)) + 1 := by
  classical
  let e : (m → K) ⊗[K] (n → K) ≃ₗ[K] Matrix m n K :=
    (TensorProduct.piScalarRight K K (m → K) n).trans
      ((Matrix.ofLinearEquiv K).trans (transposeLinearEquiv n m K K))
  have he (u : m → K) (v : n → K) : e (u ⊗ₜ[K] v) = vecMulVec u v := by
    ext i j
    simp [e, TensorProduct.piScalarRight, TensorProduct.piScalarRightHom,
      TensorProduct.piScalarRightHomBil, vecMulVec, mul_comm]
  have hc : SpanConnected K (fun i ↦ x i ⊗ₜ[K] y i) s := by
    apply (spanConnected_map_iff e.toLinearMap e.injective _ s).mp
    simpa only [Function.comp_def, LinearEquiv.coe_coe, he] using hconn
  have hh := finrank_factors_le_tensor_span_add_one_of_finite x y s (Set.toFinite _) hc
    (fun i hi hz ↦ hn i hi (by rw [← he, hz]; simp))
  have hmspan : (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' s)).map e.toLinearMap =
      Submodule.span K ((fun i ↦ vecMulVec (x i) (y i)) '' s) := by
    simp only [Submodule.map_span, Set.image_image, LinearEquiv.coe_coe, he]
  have hd := (Submodule.equivMapOfInjective e.toLinearMap e.injective
    (Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' s))).finrank_eq
  rw [hmspan] at hd
  rw [hd] at hh
  have hleft := rank_le_factor_span x y s T hT
  have htrans : Tᵀ ∈ Submodule.span K ((fun i ↦ vecMulVec (y i) (x i)) '' s) := by
    have hm := Submodule.mem_map_of_mem
      (f := (transposeLinearEquiv m n K K).toLinearMap) hT
    rw [Submodule.map_span, Set.image_image] at hm
    change Tᵀ ∈ Submodule.span K ((fun i ↦ (vecMulVec (x i) (y i))ᵀ) '' s) at hm
    simpa only [transpose_vecMulVec] using hm
  have hright := rank_le_factor_span y x s Tᵀ htrans
  rw [rank_transpose] at hright
  omega

end MMRank.RankOneFourSpace
namespace MMRank.RankOneFourSpace
open Matrix Module
variable {K I V : Type*} [Field K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Fintype I] in
/-- Одномерный канонический блок содержит один индекс, если линии различны. -/
theorem component_singleton_of_finrank_one (A : I → V)
    (hn : ∀ i, A i ≠ 0)
    (hp : Function.Injective (fun i ↦ Submodule.span K ({A i} : Set V)))
    (c : Set.range (coordinateComponent (familyWords (K := K) A)))
    (hc : finrank K (coordinateEvalSpan (familyWords (K := K) A) c.val) = 1) :
    ∃ j, c.val = {j} := by
  classical
  obtain ⟨j, hjc⟩ := c.property
  have hj : j ∈ c.val := by rw [← hjc]; exact mem_coordinateComponent_self _ j
  let e := familyEmbedding (K := K) A
  have hd := (Submodule.equivMapOfInjective e (familyEmbedding_injective (K := K) A)
    (coordinateEvalSpan (familyWords (K := K) A) c.val)).finrank_eq
  rw [familyEmbedding_map_span] at hd
  have hdim : finrank K (Submodule.span K (A '' c.val)) = 1 := hd.symm.trans hc
  have he := eq_span_singleton_of_mem_of_finrank_eq_one hdim
    (Submodule.subset_span ⟨j, hj, rfl⟩) (hn j)
  refine ⟨j, Set.ext fun i ↦ ?_⟩
  constructor
  · intro hi
    have hei := eq_span_singleton_of_mem_of_finrank_eq_one hdim
      (Submodule.subset_span ⟨i, hi, rfl⟩) (hn i)
    exact Set.mem_singleton_iff.mpr (hp (hei.symm.trans he))
  · intro hi
    exact (Set.mem_singleton_iff.mp hi) ▸ hj

/-- Без активной одномерной компоненты
связный ранговый бюджет оплачивает три ранга двумя размерностями. -/
theorem three_mul_sum_le_two_mul_sum_of_component_budget {B : Type*} [Fintype B]
    (d r : B → ℕ)
    (hr : ∀ c, 2 * r c ≤ d c + 1) (h1 : ∀ c, d c = 1 → r c = 0) :
    3 * (∑ c, r c) ≤ 2 * (∑ c, d c) := by
  classical
  have hb (c) : 3 * r c ≤ 2 * d c := by
    by_cases hd : d c = 1
    · simp [h1 c hd]
    · have := hr c
      omega
  simpa only [← Finset.mul_sum] using
    (Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hb c))

end MMRank.RankOneFourSpace

namespace MMRank.RankOneFourSpace
open Matrix Module
variable {K I n : Type*} [Field K] [Fintype I] [Fintype n] [DecidableEq n]

/-- Rank1-семья с `2 dim span A < 3 n`, содержащая единицу размера n,
имеет изолированную линию с ненулевой компонентой единицы. -/
theorem exists_linear_separator (A : I → Matrix n n K)
    (hr : ∀ i, (A i).rank = 1)
    (hp : Function.Injective (fun i ↦ Submodule.span K ({A i} : Set (Matrix n n K))))
    (hdim : 2 * finrank K (Submodule.span K (Set.range A)) < 3 * Fintype.card n)
    (hI : (1 : Matrix n n K) ∈ Submodule.span K (Set.range A)) :
    ∃ j : I, ∃ χ : Matrix n n K →ₗ[K] K,
      χ 1 = 1 ∧ χ (A j) ≠ 0 ∧ ∀ i, i ≠ j → χ (A i) = 0 := by
  classical
  let N := familyWords (K := K) A
  let e := familyEmbedding (K := K) A
  let B := Set.range (coordinateComponent N)
  let := Fintype.ofFinite B
  let W : B → Submodule K (Module.Dual K N) := fun c ↦ coordinateEvalSpan N c.val
  let d : B → ℕ := fun c ↦ finrank K (W c)
  have hi := familyEmbedding_injective (K := K) A
  have he : e.range = Submodule.span K (Set.range A) := by
    have hh := familyEmbedding_map_span (K := K) A Set.univ
    simpa only [coordinateEvalSpan_univ, Submodule.map_top, Set.image_univ] using hh
  obtain ⟨v, hv⟩ : ∃ v, e v = (1 : Matrix n n K) := by
    apply LinearMap.mem_range.mp
    rw [he]
    exact hI
  have hdirect := coordinateComponents_dual_direct N
  have hgmem : v ∈ ⨆ c ∈ (Finset.univ : Finset B), W c := by
    simp only [Finset.mem_univ, iSup_true]
    change v ∈ ⨆ c : Set.range (coordinateComponent N), coordinateEvalSpan N c.val
    rw [hdirect.2]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_iSup_finset_iff_exists_sum W v).mp hgmem
  let T : B → Matrix n n K := fun c ↦ e (g c).val
  let r : B → ℕ := fun c ↦ (T c).rank
  have hsum : (∑ c, T c) = 1 := by rw [← map_sum, hg, hv]
  have hdim' : 2 * (∑ c, d c) < 3 * Fintype.card n := by
    have hh := finrank_iSup_eq_sum_of_iSupIndep W hdirect.1
    rw [hdirect.2, finrank_top, Subspace.dual_finrank_eq] at hh
    rw [← hh]
    simpa only [N, familyWords_finrank] using hdim
  have hn (i) : A i ≠ 0 := by
    intro hz
    have hh := hr i
    simp [hz] at hh
  choose x y hxy using fun i ↦ exists_vecMulVec_of_rank_le_one (A i) (hr i).le
  have hxy' : (fun i ↦ vecMulVec (x i) (y i)) = A := funext hxy
  have hmem (c : B) : T c ∈ Submodule.span K (A '' c.val) := by
    rw [← familyEmbedding_map_span (K := K) A c.val]
    exact Submodule.mem_map_of_mem (f := e) (g c).property
  have hbound (c : B) : 2 * r c ≤ d c + 1 := by
    have hc : SpanConnected K (coordinateEval N) c.val := by
      obtain ⟨i, hi⟩ := c.property
      rw [← hi]
      exact coordinateComponent_evalSpan_connected N i
    have hc' := (spanConnected_map_iff e hi (coordinateEval N) c.val).mpr hc
    have hcA : SpanConnected K A c.val := by
      simpa only [Function.comp_def, e, N, familyEmbedding_coordinateEval] using hc'
    rw [← hxy'] at hcA
    have hm : T c ∈ Submodule.span K ((fun i ↦ vecMulVec (x i) (y i)) '' c.val) := by
      rw [hxy']; exact hmem c
    have hh := twice_rank_le_span_add_one x y c.val hcA
      (fun i _ ↦ by rw [hxy i]; exact hn i) (T c) hm
    rw [hxy'] at hh
    have hd := (Submodule.equivMapOfInjective e hi (W c)).finrank_eq
    rw [familyEmbedding_map_span] at hd
    rw [← hd] at hh
    exact hh
  obtain ⟨c, hc1, hc0⟩ : ∃ c : B, d c = 1 ∧ T c ≠ 0 := by
    by_contra! hc
    have hz (c : B) (hd : d c = 1) : r c = 0 := by simp [r, hc c hd]
    have hh := three_mul_sum_le_two_mul_sum_of_component_budget d r hbound hz
    have hb := matrix_rank_sum_le T
    rw [hsum, rank_one] at hb
    change Fintype.card n ≤ ∑ c, r c at hb
    omega
  obtain ⟨j, hcj⟩ := component_singleton_of_finrank_one A hn hp c hc1
  have hstable : ∀ w ∈ N, coordinateProjection K ({j} : Set I) w ∈ N := by
    obtain ⟨k, hk⟩ := c.property
    rw [← hcj, ← hk]
    exact coordinateComponent_stable N k
  let F := LinearMap.pi (fun i ↦ (Module.Dual.eval K (Matrix n n K)) (A i))
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K (hn j)
  have hw : F φ ∈ N := LinearMap.mem_range_self F φ
  obtain ⟨χ, hχ⟩ : ∃ χ, F χ = coordinateProjection K ({j} : Set I) (F φ) :=
    hstable (F φ) hw
  have hχcoord (i) : χ (A i) = coordinateProjection K ({j} : Set I) (F φ) i :=
    congrFun hχ i
  have hχj : χ (A j) ≠ 0 := by rw [hχcoord]; simpa [F] using hφ
  have hzero (i) (hij : i ≠ j) : χ (A i) = 0 := by rw [hχcoord]; simp [hij]
  let H := Submodule.span K (A '' ({j} : Set I)ᶜ)
  have hχH : ∀ T ∈ H, χ T = 0 := by
    have hk : H ≤ χ.ker := Submodule.span_le.mpr (by
      rintro _ ⟨i, hi, rfl⟩
      exact hzero i (by simpa using hi))
    intro T hT
    exact hk hT
  have hTc : T c ∈ Submodule.span K ({A j} : Set (Matrix n n K)) := by
    simpa only [hcj, Set.image_singleton] using hmem c
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hTc
  have ha0 : a ≠ 0 := by intro hz; apply hc0; rw [← ha, hz, zero_smul]
  have hχTc : χ (T c) ≠ 0 := by rw [← ha, map_smul, smul_eq_mul]; exact mul_ne_zero ha0 hχj
  have hχI : χ (1 : Matrix n n K) ≠ 0 := by
    have hh : χ (1 : Matrix n n K) = χ (T c) := by
      rw [← hsum, map_sum]
      apply Finset.sum_eq_single c
      · intro b _ hbc
        have hd := coordinateBlocks_pairwise_disjoint N hbc
        have hbj : j ∉ b.val := fun hj ↦ Set.disjoint_left.mp hd hj (by rw [hcj]; simp)
        have hm : T b ∈ H := Submodule.span_mono (Set.image_mono
          (fun i hib ↦ by intro hij; subst i; exact hbj hib)) (hmem b)
        exact hχH _ hm
      · simp
    rwa [hh]
  refine ⟨j, (χ 1)⁻¹ • χ, ?_, ?_, ?_⟩
  · simp [hχI]
  · simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_ne_zero (inv_ne_zero hχI) hχj
  · intro i hij
    simp [hzero i hij]

/-- Линейный и квадратичный разделители одной линии. Поле произвольно;
квадратичная форма инвариантна при добавлении скалярной единицы. -/
theorem exists_linear_quadratic_separator (A : I → Matrix n n K)
    (hsize : 3 ≤ Fintype.card n) (hr : ∀ i, (A i).rank = 1)
    (hp : Function.Injective (fun i ↦ Submodule.span K ({A i} : Set (Matrix n n K))))
    (hdim : finrank K (Submodule.span K (Set.range A)) ≤ 4)
    (hI : (1 : Matrix n n K) ∈ Submodule.span K (Set.range A)) :
    ∃ j : I, ∃ χ : Matrix n n K →ₗ[K] K, ∃ Q : QuadraticForm K (Matrix n n K),
      χ 1 = 1 ∧ χ (A j) ≠ 0 ∧ Q (A j) ≠ 0 ∧
      (∀ i, i ≠ j → χ (A i) = 0 ∧ Q (A i) = 0) ∧
      (∀ (T : Matrix n n K) (c : K), Q (T + c • 1) = Q T) := by
  obtain ⟨j, χ, hχI, hχj, hzero⟩ := exists_linear_separator A hr hp (by omega) hI
  obtain ⟨Q, hQj, hQzero, hQI⟩ := exists_quadratic_separator_of_linear hsize A j χ
    hχI hχj (fun i ↦ (hr i).le) hzero
  exact ⟨j, χ, Q, hχI, hχj, hQj, fun i hi ↦ ⟨hzero i hi, hQzero i hi⟩, hQI⟩

end MMRank.RankOneFourSpace
