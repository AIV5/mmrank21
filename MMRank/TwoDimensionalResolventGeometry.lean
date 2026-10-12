module

public import MMRank.RegularMatrixPencil
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-! # Двумерная геометрия резольвентного уравнения

Корни характеристического
многочлена и тождество Кэли—Гамильтона заменяют выбор диагонального или
жорданова базиса. Совпадение корней и произвольная характеристика разрешены.
Алгебраическая замкнутость нужна только для выбора двух корней.
-/

namespace MMRank
open Matrix Module Polynomial

variable {K : Type*} [Field K]

/-- У матрицы ранга один на двумерном пространстве ядро одномерно. -/
theorem twoDimensional_finrank_kernel_of_rank_one
    (T : Matrix (Fin 2) (Fin 2) K) (hT : T.rank = 1) :
    finrank K T.mulVecLin.ker = 1 := by
  have h := T.mulVecLin.finrank_range_add_finrank_ker
  change T.rank + finrank K T.mulVecLin.ker = finrank K (Fin 2 → K) at h
  simp only [hT, finrank_pi, Fintype.card_fin] at h
  omega

/-- Любой ненулевой вектор ядра матрицы ранга один порождает это ядро. -/
theorem twoDimensional_rank_one_kernel_eq_span
    (T : Matrix (Fin 2) (Fin 2) K) (hT : T.rank = 1)
    (p : Fin 2 → K) (hp : p ≠ 0) (hTp : T *ᵥ p = 0) :
    T.mulVecLin.ker = K ∙ p :=
  eq_span_singleton_of_mem_of_finrank_eq_one
    (twoDimensional_finrank_kernel_of_rank_one T hT) (by simpa using hTp) hp

/-- Выбор ненулевого генератора ядра не требует замкнутости поля. -/
theorem twoDimensional_rank_one_kernel
    (T : Matrix (Fin 2) (Fin 2) K) (hT : T.rank = 1) :
    ∃ p : Fin 2 → K, p ≠ 0 ∧ T.mulVecLin.ker = K ∙ p := by
  have hdim := twoDimensional_finrank_kernel_of_rank_one T hT
  have hker : T.mulVecLin.ker ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨p, hp0, eq_span_singleton_of_mem_of_finrank_eq_one hdim hp hp0⟩

/-- Если ядро левого множителя — одна линия, все столбцы зануляемого
произведения лежат на этой линии. Число столбцов произвольно. -/
theorem matrix_mem_fixedColumnSpace_of_mul_eq_zero
    {P Q : Type*} [Fintype P]
    (T : Matrix P P K) (p : P → K) (hker : T.mulVecLin.ker = K ∙ p)
    (X : Matrix P Q K) (hX : T * X = 0) : X ∈ fixedColumnSpace p := by
  classical
  have hc (j : Q) : ∃ c : K, c • p = fun i ↦ X i j := by
    apply Submodule.mem_span_singleton.mp
    rw [← hker]
    apply LinearMap.mem_ker.mpr
    ext i
    change (T * X) i j = 0
    exact congrFun (congrFun hX i) j
  choose q hq using hc
  refine ⟨q, ?_⟩
  change vecMulVec p q = X
  ext i j
  simpa [vecMulVec, mul_comm] using congrFun (hq j) i

/-- Нескалярный двумерный оператор имеет два, возможно совпадающих,
собственных параметра. Оба сдвига ненулевые ранга один; вне этих
параметров сдвиг обратим. -/
theorem exists_twoDimensional_resolvent_roots [IsAlgClosed K]
    (H : Matrix (Fin 2) (Fin 2) K)
    (hH : ∀ a : K, H ≠ a • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ lam mu : K,
      (∀ t : K, (t • (1 : Matrix (Fin 2) (Fin 2) K) - H).det =
        (t - lam) * (t - mu)) ∧
      (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) *
        (mu • (1 : Matrix (Fin 2) (Fin 2) K) - H) = 0 ∧
      (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H).rank = 1 ∧
      (mu • (1 : Matrix (Fin 2) (Fin 2) K) - H).rank = 1 := by
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root H.charpoly
    (by simp [Matrix.charpoly_degree_eq_dim])
  let mu := H.trace - lam
  have hr : lam ^ 2 - H.trace * lam + H.det = 0 := by
    simpa [Matrix.charpoly_fin_two] using hlam.eq_zero
  have hd : H.det = lam * mu := by
    dsimp [mu]
    linear_combination hr
  have ht : H.trace = lam + mu := by dsimp [mu]; ring
  have hpoly : H.charpoly = (C lam - X) * (C mu - X) := by
    rw [Matrix.charpoly_fin_two, hd, ht]
    simp only [map_add, map_mul]
    ring
  have hdet (t : K) : (t • (1 : Matrix (Fin 2) (Fin 2) K) - H).det =
      (t - lam) * (t - mu) := by
    have hs : Matrix.scalar (Fin 2) t = t • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply]
    rw [← hs, ← Matrix.eval_charpoly, hpoly]
    simp only [eval_mul, eval_sub, eval_C, eval_X]
    ring
  have hCH : (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) *
      (mu • (1 : Matrix (Fin 2) (Fin 2) K) - H) = 0 := by
    have h := H.aeval_self_charpoly
    rw [hpoly] at h
    simpa only [map_mul, map_sub, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one] using h
  have hrank (t : K) (ht0 : (t • (1 : Matrix (Fin 2) (Fin 2) K) - H).det = 0) :
      (t • (1 : Matrix (Fin 2) (Fin 2) K) - H).rank = 1 := by
    let T := t • (1 : Matrix (Fin 2) (Fin 2) K) - H
    have hn : T ≠ 0 := by
      intro hz
      exact hH t (sub_eq_zero.mp hz).symm
    have hpos := mt (matrix_rank_eq_zero_iff T).mp hn
    have hle : T.rank ≤ 2 := T.rank_le_width
    have htwo : T.rank ≠ 2 := by
      intro htwo
      have hu := (matrix_isUnit_iff_rank_eq_card T).mpr (by simpa using htwo)
      have hud := (Matrix.isUnit_iff_isUnit_det T).mp hu
      exact not_isUnit_zero (ht0 ▸ hud)
    change T.rank = 1
    omega
  exact ⟨lam, mu, hdet, hCH, hrank lam (by simp [hdet]), hrank mu (by simp [hdet])⟩

/-- Обратимость сдвига вне двух корней следует непосредственно из определителя. -/
theorem isUnit_resolvent_shift_of_det_factorization
    (H : Matrix (Fin 2) (Fin 2) K) (lam mu t : K)
    (hdet : (t • (1 : Matrix (Fin 2) (Fin 2) K) - H).det = (t - lam) * (t - mu))
    (hlam : t ≠ lam) (hmu : t ≠ mu) :
    IsUnit (t • (1 : Matrix (Fin 2) (Fin 2) K) - H) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [hdet]
  exact IsUnit.mk0 _ (mul_ne_zero (sub_ne_zero.mpr hlam) (sub_ne_zero.mpr hmu))

/-- Обратимый левый множитель сохраняет общий второй внешний фактор. -/
theorem exists_outerFactor_of_isUnit_mul
    {P Q : Type*} [Fintype P] [DecidableEq P]
    (T : Matrix P P K) (hT : IsUnit T) (X : Matrix P Q K)
    (p : P → K) (q : Q → K) (z : K) (hX : T * X = z • vecMulVec p q) :
    ∃ v : P → K, vecMulVec v q = X := by
  obtain ⟨u, hu⟩ := hT
  have hx : X = (↑u⁻¹ : Matrix P P K) * (z • vecMulVec p q) := by
    calc X = (↑u⁻¹ : Matrix P P K) * ((↑u : Matrix P P K) * X) := by
           simp [← Matrix.mul_assoc]
         _ = (↑u⁻¹ : Matrix P P K) * (z • vecMulVec p q) := by rw [hu, hX]
  refine ⟨z • ((↑u⁻¹ : Matrix P P K) *ᵥ p), ?_⟩
  rw [hx, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.smul_vecMulVec]

/-- Левый аннулятор, не зануляющий первый внешний фактор, зануляет
коэффициент правой части. Размеры и число столбцов произвольны. -/
theorem scalar_eq_zero_of_left_annihilator
    {P Q R : Type*} [Fintype P]
    (L : Matrix R P K) (T : Matrix P P K) (hLT : L * T = 0)
    (X : Matrix P Q K) (p : P → K) (q : Q → K) (z : K)
    (hp : L *ᵥ p ≠ 0) (hq : q ≠ 0) (hX : T * X = z • vecMulVec p q) :
    z = 0 ∧ T * X = 0 := by
  have h : z • vecMulVec (L *ᵥ p) q = 0 := by
    rw [← Matrix.mul_vecMulVec, ← Matrix.mul_smul, ← hX,
      ← Matrix.mul_assoc, hLT, Matrix.zero_mul]
  have hn : vecMulVec (L *ᵥ p) q ≠ 0 := by
    intro hz
    exact (not_or.mpr ⟨hp, hq⟩) ((MMRank.outerProduct_eq_zero_iff _ _).mp hz)
  have hz : z = 0 := (smul_eq_zero.mp h).resolve_right hn
  exact ⟨hz, by simpa [hz] using hX⟩

/-- Два скалярных сдвига одного оператора коммутируют. -/
theorem resolvent_shifts_commute {P : Type*} [Fintype P] [DecidableEq P]
    (H : Matrix P P K) (lam mu : K) :
    (lam • (1 : Matrix P P K) - H) * (mu • (1 : Matrix P P K) - H) =
      (mu • (1 : Matrix P P K) - H) * (lam • (1 : Matrix P P K) - H) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul]
  rw [mul_comm lam mu]
  abel

/-- На собственном параметре первый фактор, не являющийся собственным
вектором, вынуждает нулевую правую часть резольвентного уравнения. -/
theorem resolvent_root_of_not_eigenvector
    {Q : Type*} (H : Matrix (Fin 2) (Fin 2) K) (lam mu : K)
    (hCH : (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) *
      (mu • (1 : Matrix (Fin 2) (Fin 2) K) - H) = 0)
    (X : Matrix (Fin 2) Q K) (p : Fin 2 → K) (q : Q → K) (z : K)
    (hp : ∀ a : K, H *ᵥ p ≠ a • p) (hq : q ≠ 0)
    (hX : (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) * X = z • vecMulVec p q) :
    z = 0 ∧ (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) * X = 0 := by
  apply scalar_eq_zero_of_left_annihilator
    (mu • (1 : Matrix (Fin 2) (Fin 2) K) - H) _
    (by rw [← resolvent_shifts_commute H lam mu]; exact hCH) X p q z _ hq hX
  intro hz
  apply hp mu
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Кэли—Гамильтон превращает произведение с произвольным сдвигом
в скалярное кратное одного из двух собственных сдвигов. -/
theorem resolvent_left_shift_mul_shift
    {P : Type*} [Fintype P] [DecidableEq P]
    (H : Matrix P P K) (lam mu t : K)
    (hCH : (lam • (1 : Matrix P P K) - H) * (mu • (1 : Matrix P P K) - H) = 0) :
    (lam • (1 : Matrix P P K) - H) * (t • (1 : Matrix P P K) - H) =
      (t - mu) • (lam • (1 : Matrix P P K) - H) := by
  have ht : t • (1 : Matrix P P K) - H =
      (mu • (1 : Matrix P P K) - H) + (t - mu) • (1 : Matrix P P K) := by
    rw [sub_smul]
    abel
  rw [ht, Matrix.mul_add, hCH, Matrix.mul_smul, Matrix.mul_one, zero_add]

/-- Если первый фактор — собственный вектор для lam, то на всех параметрах
t ≠ mu резольвентное уравнение помещает X в эту столбцовую линию.
Это включает t = lam при различных корнях. -/
theorem resolvent_mem_fixedColumnSpace_of_eigenvector
    {Q : Type*} (H : Matrix (Fin 2) (Fin 2) K) (lam mu t : K)
    (hCH : (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) *
      (mu • (1 : Matrix (Fin 2) (Fin 2) K) - H) = 0)
    (hrank : (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H).rank = 1)
    (p : Fin 2 → K) (hp : p ≠ 0) (heigen : H *ᵥ p = lam • p)
    (X : Matrix (Fin 2) Q K) (q : Q → K) (z : K)
    (hX : (t • (1 : Matrix (Fin 2) (Fin 2) K) - H) * X = z • vecMulVec p q)
    (ht : t ≠ mu) : X ∈ fixedColumnSpace p := by
  have hTp : (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) *ᵥ p = 0 := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, heigen]
  apply matrix_mem_fixedColumnSpace_of_mul_eq_zero _ p
    (twoDimensional_rank_one_kernel_eq_span _ hrank p hp hTp) X
  have hzero : (t - mu) • ((lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) * X) = 0 := by
    rw [← Matrix.smul_mul, ← resolvent_left_shift_mul_shift H lam mu t hCH,
      Matrix.mul_assoc, hX, Matrix.mul_smul, Matrix.mul_vecMulVec, hTp]
    simp
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ht)

/-- Любое собственное значение принадлежит паре корней тождества
резольвентных сдвигов. Поле и размер оператора произвольны. -/
theorem eigenvalue_eq_root_of_resolvent_product
    {P : Type*} [Fintype P] [DecidableEq P]
    (H : Matrix P P K) (lam mu a : K)
    (hCH : (lam • (1 : Matrix P P K) - H) * (mu • (1 : Matrix P P K) - H) = 0)
    (p : P → K) (hp : p ≠ 0) (heigen : H *ᵥ p = a • p) : a = lam ∨ a = mu := by
  have he (s : K) : (s • (1 : Matrix P P K) - H) *ᵥ p = (s - a) • p := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heigen, sub_smul]
  have hz := congrArg (fun M : Matrix P P K ↦ M *ᵥ p) hCH
  rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, he, smul_smul,
    Matrix.zero_mulVec] at hz
  rcases mul_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hp) with hmu | hlam
  · exact Or.inr (sub_eq_zero.mp hmu).symm
  · exact Or.inl (sub_eq_zero.mp hlam).symm

open scoped Classical

/-- Нулевая правая часть резольвентных уравнений помещает все матрицы
в две столбцовые линии, поэтому при бюджете два на линию индексов не
больше четырёх. Число столбцов и размеры носителя произвольны. -/
theorem zero_resolvent_card_le_four [IsAlgClosed K]
    {Q I : Type*} [DecidableEq I]
    (G : Finset I) (H : Matrix (Fin 2) (Fin 2) K)
    (hH : ∀ a : K, H ≠ a • (1 : Matrix (Fin 2) (Fin 2) K))
    (X : I → Matrix (Fin 2) Q K) (t : I → K)
    (hres : ∀ i ∈ G, (t i • (1 : Matrix (Fin 2) (Fin 2) K) - H) * X i = 0)
    (hcol : ∀ p : Fin 2 → K, p ≠ 0 →
      (G.filter fun i ↦ X i ∈ fixedColumnSpace p).card ≤ 2) : G.card ≤ 4 := by
  classical
  obtain ⟨lam, mu, hdet, _, hrlam, hrmu⟩ := exists_twoDimensional_resolvent_roots H hH
  obtain ⟨plam, hplam, hklam⟩ := twoDimensional_rank_one_kernel _ hrlam
  obtain ⟨pmu, hpmu, hkmu⟩ := twoDimensional_rank_one_kernel _ hrmu
  let L := G.filter fun i ↦ X i ∈ fixedColumnSpace plam
  let M := G.filter fun i ↦ X i ∈ fixedColumnSpace pmu
  have hL : L.card ≤ 2 := hcol plam hplam
  have hM : M.card ≤ 2 := hcol pmu hpmu
  have hcover : G ⊆ L ∪ M := by
    intro i hi
    have hz := hres i hi
    by_cases hlam : t i = lam
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨hi, matrix_mem_fixedColumnSpace_of_mul_eq_zero
        _ plam hklam (X i) (by simpa [hlam] using hz)⟩
    by_cases hmu : t i = mu
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨hi, matrix_mem_fixedColumnSpace_of_mul_eq_zero
        _ pmu hkmu (X i) (by simpa [hmu] using hz)⟩
    obtain ⟨v, hv⟩ := exists_outerFactor_of_isUnit_mul _
      (isUnit_resolvent_shift_of_det_factorization H lam mu (t i) (hdet _) hlam hmu)
      (X i) (0 : Fin 2 → K) (0 : Q → K) 0 (by simpa using hz)
    have hx : X i = 0 := by
      rw [← hv]
      ext a b
      simp [Matrix.vecMulVec]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, by simp [hx]⟩))
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le L M)
  omega

/-- Семь резольвентных уравнений с классами мощности не больше двух
вынуждают ранг общей правой матрицы не меньше двух. Дополнительный
физический вход — запрет одного столбцового класса на каждом носителе
`t_i ≠ a`. Коэффициенты z произвольны, в частности допустимы w_i/c_i.
Нулевые X также разрешены, если классовые бюджеты учитывают их. -/
theorem twoDimensional_resolvent_rank_ge_two [IsAlgClosed K]
    {Q I : Type*} [Fintype Q] [DecidableEq I]
    (G : Finset I) (hG : 7 ≤ G.card)
    (H : Matrix (Fin 2) (Fin 2) K)
    (hH : ∀ a : K, H ≠ a • (1 : Matrix (Fin 2) (Fin 2) K))
    (X : I → Matrix (Fin 2) Q K) (t z : I → K) (A : Matrix (Fin 2) Q K)
    (hres : ∀ i ∈ G, (t i • (1 : Matrix (Fin 2) (Fin 2) K) - H) * X i = z i • A)
    (hcol : ∀ p : Fin 2 → K, p ≠ 0 →
      (G.filter fun i ↦ X i ∈ fixedColumnSpace p).card ≤ 2)
    (hrow : ∀ q : Q → K, q ≠ 0 →
      (G.filter fun i ↦ (X i).transpose ∈ fixedColumnSpace q).card ≤ 2)
    (hspread : ∀ a : K, ∀ p : Fin 2 → K, p ≠ 0 →
      ¬ (∀ i ∈ G, t i ≠ a → X i ∈ fixedColumnSpace p)) : 2 ≤ A.rank := by
  classical
  obtain ⟨lam, mu, hdet, hCH, hrlam, hrmu⟩ := exists_twoDimensional_resolvent_roots H hH
  obtain ⟨plam, hplam, hklam⟩ := twoDimensional_rank_one_kernel _ hrlam
  obtain ⟨pmu, hpmu, hkmu⟩ := twoDimensional_rank_one_kernel _ hrmu
  let L := G.filter fun i ↦ X i ∈ fixedColumnSpace plam
  let M := G.filter fun i ↦ X i ∈ fixedColumnSpace pmu
  have hL : L.card ≤ 2 := hcol plam hplam
  have hM : M.card ≤ 2 := hcol pmu hpmu
  have hCH' : (mu • (1 : Matrix (Fin 2) (Fin 2) K) - H) *
      (lam • (1 : Matrix (Fin 2) (Fin 2) K) - H) = 0 := by
    rw [← resolvent_shifts_commute H lam mu]
    exact hCH
  by_contra hlow
  have hA : A.rank ≤ 1 := by omega
  by_cases hA0 : A = 0
  · have hc := zero_resolvent_card_le_four G H hH X t
      (fun i hi ↦ by simpa [hA0] using hres i hi) hcol
    omega
  obtain ⟨p, q, hpq⟩ := exists_vecMulVec_of_rank_le_one A hA
  have hpq0 : vecMulVec p q ≠ 0 := fun h ↦ hA0 (hpq.symm.trans h)
  have hp : p ≠ 0 := fun h ↦ hpq0 ((MMRank.outerProduct_eq_zero_iff _ _).mpr (Or.inl h))
  have hq : q ≠ 0 := fun h ↦ hpq0 ((MMRank.outerProduct_eq_zero_iff _ _).mpr (Or.inr h))
  have heq (i : I) (hi : i ∈ G) :
      (t i • (1 : Matrix (Fin 2) (Fin 2) K) - H) * X i = z i • vecMulVec p q := by
    rw [hpq]
    exact hres i hi
  by_cases heigen : ∃ a : K, H *ᵥ p = a • p
  · obtain ⟨a, ha⟩ := heigen
    rcases eigenvalue_eq_root_of_resolvent_product H lam mu a hCH p hp ha with ha' | ha'
    · apply hspread mu p hp
      intro i hi hti
      exact resolvent_mem_fixedColumnSpace_of_eigenvector H lam mu (t i) hCH hrlam p hp
        (by simpa [ha'] using ha) (X i) q (z i) (heq i hi) hti
    · apply hspread lam p hp
      intro i hi hti
      exact resolvent_mem_fixedColumnSpace_of_eigenvector H mu lam (t i) hCH' hrmu p hp
        (by simpa [ha'] using ha) (X i) q (z i) (heq i hi) hti
  have hne : ∀ a : K, H *ᵥ p ≠ a • p := fun a ha ↦ heigen ⟨a, ha⟩
  let R := G.filter fun i ↦ (X i).transpose ∈ fixedColumnSpace q
  have hR : R.card ≤ 2 := hrow q hq
  have hcover : G ⊆ (L ∪ M) ∪ R := by
    intro i hi
    by_cases hlam : t i = lam
    · have hx := (resolvent_root_of_not_eigenvector H lam mu hCH (X i) p q (z i)
        hne hq (by simpa [hlam] using heq i hi)).2
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hi, matrix_mem_fixedColumnSpace_of_mul_eq_zero
          _ plam hklam (X i) hx⟩))))
    by_cases hmu : t i = mu
    · have hx := (resolvent_root_of_not_eigenvector H mu lam hCH' (X i) p q (z i)
        hne hq (by simpa [hmu] using heq i hi)).2
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hi, matrix_mem_fixedColumnSpace_of_mul_eq_zero
          _ pmu hkmu (X i) hx⟩))))
    obtain ⟨v, hv⟩ := exists_outerFactor_of_isUnit_mul _
      (isUnit_resolvent_shift_of_det_factorization H lam mu (t i) (hdet _) hlam hmu)
      (X i) p q (z i) (heq i hi)
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    refine ⟨hi, ⟨v, ?_⟩⟩
    change vecMulVec q v = (X i).transpose
    rw [← hv, Matrix.transpose_vecMulVec]
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le (L ∪ M) R)
  have hLM := Finset.card_union_le L M
  omega

end MMRank
