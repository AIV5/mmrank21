import MMRank.RankOneMatrixSpaces
import MMRank.JointSymmetrizers
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Вместимость совместных симметризаторов двух трёхмерных блоков

Двойственный закон симметрии имеет вид
A[k]×+B[l]×=0. При общем нулевом ядре A,B он заставляет k×l=0.
Классификация пространств ранга≤1 применяется только к этому ядру 3×2,
не к пространствам сингулярных блоков алгоритма. Все характеристики.
-/

namespace MMRank
open Matrix Module
open scoped Matrix
variable {K S : Type*} [Field K] [Fintype S]

/-- Матрица внешнего произведения w↦k×w, включая характеристику два. -/
def crossMatrix : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K where
  toFun k := !![0, -k 2, k 1; k 2, 0, -k 0; -k 1, k 0, 0]
  map_add' k l := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' a k := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem crossMatrix_mulVec (k w : Fin 3 → K) : crossMatrix k *ᵥ w = k ⨯₃ w := by
  ext i
  fin_cases i <;> simp [crossMatrix, mulVec, dotProduct, Fin.sum_univ_succ, cross_apply]
  all_goals ring

theorem crossMatrix_eq_zero_iff (k : Fin 3 → K) : crossMatrix k = 0 ↔ k = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · simpa [crossMatrix] using congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 2 1) h
    · simpa [crossMatrix] using congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 0 2) h
    · simpa [crossMatrix] using congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 1 0) h
  · rintro rfl
    exact map_zero crossMatrix

theorem exists_smul_of_cross_eq_zero (k w : Fin 3 → K) (hk : k ≠ 0)
    (h : k ⨯₃ w = 0) : ∃ a : K, w = a • k := by
  have hn : ¬ LinearIndependent K ![k, w] := by
    intro hi
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr hi) h
  rw [LinearIndependent.pair_iff' hk] at hn
  push Not at hn
  obtain ⟨a, ha⟩ := hn
  exact ⟨a, ha.symm⟩

/-- Ненулевая матрица может занулять [k]× лишь на одной прямой параметров k. -/
theorem finrank_cross_composition_ker_le_one (A : Matrix S (Fin 3) K) (hA : A ≠ 0) :
    finrank K ((mulLeftLinearMap (Fin 3) K A).comp crossMatrix).ker ≤ 1 := by
  classical
  obtain ⟨s, i, hsi⟩ : ∃ s i, A s i ≠ 0 := by
    by_contra! hh
    apply hA
    ext s i
    exact hh s i
  let r := A s
  have hr : r ≠ 0 := fun hh ↦ hsi (congrFun hh i)
  have hk : ((mulLeftLinearMap (Fin 3) K A).comp crossMatrix).ker ≤ Submodule.span K {r} := by
    intro k hk
    have he : A * crossMatrix k = 0 := hk
    have hc : r ⨯₃ k = 0 := by
      have h0 := congrArg (fun T : Matrix S (Fin 3) K ↦ T s 0) he
      have h1 := congrArg (fun T : Matrix S (Fin 3) K ↦ T s 1) he
      have h2 := congrArg (fun T : Matrix S (Fin 3) K ↦ T s 2) he
      ext j
      fin_cases j
      · simpa [r, crossMatrix, cross_apply, mul_apply, Fin.sum_univ_succ, sub_eq_add_neg] using h0
      · simpa [r, crossMatrix, cross_apply, mul_apply, Fin.sum_univ_succ, sub_eq_add_neg,
          add_comm] using h1
      · simpa [r, crossMatrix, cross_apply, mul_apply, Fin.sum_univ_succ, sub_eq_add_neg] using h2
    obtain ⟨a, ha⟩ := exists_smul_of_cross_eq_zero r k hr hc
    rw [ha]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  exact (Submodule.finrank_mono hk).trans_eq (finrank_span_singleton hr)

/-- Два кососимметричных множителя в двойственном уравнении. -/
def pairCrossMap (A B : Matrix S (Fin 3) K) :
    Matrix (Fin 3) (Fin 2) K →ₗ[K] Matrix S (Fin 3) K where
  toFun X := A * crossMatrix (fun i ↦ X i 0) + B * crossMatrix (fun i ↦ X i 1)
  map_add' X Y := by
    change A * crossMatrix ((fun i ↦ X i 0) + (fun i ↦ Y i 0)) +
      B * crossMatrix ((fun i ↦ X i 1) + (fun i ↦ Y i 1)) = _
    rw [map_add, map_add, Matrix.mul_add, Matrix.mul_add]
    abel
  map_smul' a X := by
    change A * crossMatrix (a • (fun i ↦ X i 0)) + B * crossMatrix (a • (fun i ↦ X i 1)) = _
    rw [map_smul, map_smul, Matrix.mul_smul, Matrix.mul_smul, smul_add]
    rfl

omit [Fintype S] in
theorem pairCrossMap_outer (A B : Matrix S (Fin 3) K)
    (w : Fin 3 → K) (a : Fin 2 → K) :
    pairCrossMap A B (vecMulVec w a) = (a 0 • A + a 1 • B) * crossMatrix w := by
  have he (j : Fin 2) : (fun i ↦ vecMulVec w a i j) = a j • w := by
    ext i
    simp [vecMulVec, mul_comm]
  simp only [pairCrossMap, LinearMap.coe_mk, AddHom.coe_mk, he, map_smul,
    Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]

omit [Fintype S] in
/-- Нулевое общее ядро превращает каждую пару в ядре f в матрицу ранга≤1. -/
theorem pairCrossMap_kernel_rank_le_one (A B : Matrix S (Fin 3) K)
    (hk : ∀ u, A *ᵥ u = 0 → B *ᵥ u = 0 → u = 0)
    (X : Matrix (Fin 3) (Fin 2) K) (hX : X ∈ (pairCrossMap A B).ker) : X.rank ≤ 1 := by
  let k := fun i ↦ X i 0
  let l := fun i ↦ X i 1
  have he : A * crossMatrix k + B * crossMatrix l = 0 := hX
  have hAk : A *ᵥ (k ⨯₃ l) = 0 := by
    have hh := congrArg (fun T : Matrix S (Fin 3) K ↦ T *ᵥ l) he
    simpa only [add_mulVec, ← mulVec_mulVec, crossMatrix_mulVec, cross_self,
      mulVec_zero, zero_mulVec, add_zero] using hh
  have hBk : B *ᵥ (k ⨯₃ l) = 0 := by
    have hh := congrArg (fun T : Matrix S (Fin 3) K ↦ T *ᵥ k) he
    have hanti : l ⨯₃ k = -(k ⨯₃ l) := (cross_anticomm k l).symm
    simpa only [add_mulVec, ← mulVec_mulVec, crossMatrix_mulVec, cross_self, hanti,
      mulVec_zero, zero_mulVec, zero_add, mulVec_neg, neg_eq_zero] using hh
  have hc : k ⨯₃ l = 0 := hk _ hAk hBk
  by_cases hk0 : k = 0
  · have hx : X = vecMulVec l ![0, 1] := by
      ext i j
      fin_cases j
      · simpa [vecMulVec, k] using congrFun hk0 i
      · simp [vecMulVec, l]
    rw [hx]
    exact rank_vecMulVec_le _ _
  · obtain ⟨a, ha⟩ := exists_smul_of_cross_eq_zero k l hk0 hc
    have hx : X = vecMulVec k ![1, a] := by
      ext i j
      fin_cases j
      · simp [vecMulVec, k]
      · simpa [vecMulVec, l, Pi.smul_apply, mul_comm] using congrFun ha i
    rw [hx]
    exact rank_vecMulVec_le _ _

/-- Для независимых блоков с общим нулевым ядром двойственное уравнение
имеет ядро размерности≤1. -/
theorem finrank_pairCrossMap_ker_le_one (A B : Matrix S (Fin 3) K)
    (hk : ∀ u, A *ᵥ u = 0 → B *ᵥ u = 0 → u = 0)
    (hab : ∀ a b : K, a • A + b • B = 0 → a = 0 ∧ b = 0) :
    finrank K (pairCrossMap A B).ker ≤ 1 := by
  classical
  let N := (pairCrossMap A B).ker
  by_contra! hn
  change 1 < finrank K N at hn
  have hNb : N ≠ ⊥ := by
    intro hh
    rw [hh, finrank_bot] at hn
    omega
  obtain ⟨X, hX, hX0⟩ := N.ne_bot_iff.mp hNb
  rcases rank_le_one_space_common_factor N (pairCrossMap_kernel_rank_le_one A B hk) with
    ⟨w, hw⟩ | ⟨a, ha⟩
  · have hw0 : w ≠ 0 := by
      intro hh
      obtain ⟨a, he⟩ := hw X hX
      apply hX0
      ext i j
      simp [← he, hh, vecMulVec]
    let J : (Fin 2 → K) →ₗ[K] Matrix (Fin 3) (Fin 2) K := vecMulVecBilin K K w
    have hi : Function.Injective J := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro a ha
      exact (outerProduct_eq_zero_iff w a).mp ha |>.resolve_left hw0
    have hNJ : N ≤ J.range := by
      intro Y hY
      obtain ⟨a, he⟩ := hw Y hY
      exact ⟨a, he⟩
    have hd : finrank K J.range = 2 := by rw [LinearMap.finrank_range_of_inj hi]; simp
    have hle := Submodule.finrank_mono hNJ
    have hJN : J.range = N := Submodule.eq_of_le_of_finrank_eq hNJ (by omega) |>.symm
    have heA : A * crossMatrix w = 0 := by
      have hh : vecMulVec w ![1, 0] ∈ N := hJN ▸ (show vecMulVec w ![1, 0] ∈ J.range from ⟨_, rfl⟩)
      change pairCrossMap A B (vecMulVec w ![1, 0]) = 0 at hh
      rw [pairCrossMap_outer] at hh
      simpa using hh
    have heB : B * crossMatrix w = 0 := by
      have hh : vecMulVec w ![0, 1] ∈ N := hJN ▸ (show vecMulVec w ![0, 1] ∈ J.range from ⟨_, rfl⟩)
      change pairCrossMap A B (vecMulVec w ![0, 1]) = 0 at hh
      rw [pairCrossMap_outer] at hh
      simpa using hh
    have hz : crossMatrix w = 0 := by
      ext i j
      have h := hk (crossMatrix w *ᵥ Pi.single j 1)
        (by rw [mulVec_mulVec, heA, zero_mulVec])
        (by rw [mulVec_mulVec, heB, zero_mulVec])
      simpa using congrFun h i
    exact hw0 ((crossMatrix_eq_zero_iff w).mp hz)
  · have ha0 : a ≠ 0 := by
      intro hh
      obtain ⟨w, he⟩ := ha X hX
      apply hX0
      ext i j
      simp [← he, hh, vecMulVec]
    let T := a 0 • A + a 1 • B
    have hT : T ≠ 0 := by
      intro hh
      obtain ⟨h0, h1⟩ := hab (a 0) (a 1) hh
      apply ha0
      ext j
      fin_cases j <;> assumption
    let J : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 2) K := (vecMulVecBilin K K).flip a
    have hle : N ≤ ((mulLeftLinearMap (Fin 3) K T).comp crossMatrix).ker.map J := by
      intro Y hY
      obtain ⟨w, he⟩ := ha Y hY
      refine ⟨w, ?_, he⟩
      have hh : pairCrossMap A B (vecMulVec w a) = 0 := by rw [he]; exact hY
      change T * crossMatrix w = 0
      simpa only [pairCrossMap_outer] using hh
    have hb := (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)
    have hc := finrank_cross_composition_ker_le_one T hT
    omega

/-- Следовая двойственность между противоположными прямоугольными матрицами. -/
def rectangularTraceDual : Matrix S (Fin 3) K →ₗ[K] Dual K (Matrix (Fin 3) S K) where
  toFun A :=
    { toFun M := trace (M * A)
      map_add' M N := by simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' a M := by simp [Matrix.smul_mul] }
  map_add' A B := by ext M; simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' a A := by ext M; simp [Matrix.mul_smul]

theorem rectangularTraceDual_injective : Function.Injective (rectangularTraceDual (K := K) (S := S)) := by
  intro A B h
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro M
  exact congrArg (fun φ : Dual K (Matrix (Fin 3) S K) ↦ φ M) h

/-- Симметричная матрица ортогональна [k]× без деления на два. -/
theorem trace_mul_crossMatrix_eq_zero_of_isSymm (A : Matrix (Fin 3) (Fin 3) K)
    (hA : A.IsSymm) (k : Fin 3 → K) : trace (A * crossMatrix k) = 0 := by
  have h10 := hA.apply 0 1
  have h20 := hA.apply 0 2
  have h21 := hA.apply 1 2
  simp [trace, Matrix.mul_apply, Fin.sum_univ_succ, crossMatrix] at *
  rw [h10, h20, h21]
  ring

/-- Два независимых блока с нулевым общим ядром накладывают не менее
пяти независимых линейных условий симметрии. Число строк S произвольно. -/
theorem finrank_add_five_le_of_two_jointSymmetrizers
    (A B : Matrix S (Fin 3) K)
    (hk : ∀ u, A *ᵥ u = 0 → B *ᵥ u = 0 → u = 0)
    (hab : ∀ a b : K, a • A + b • B = 0 → a = 0 ∧ b = 0)
    (H : Submodule K (Matrix (Fin 3) S K))
    (hA : ∀ M ∈ H, (M * A).IsSymm) (hB : ∀ M ∈ H, (M * B).IsSymm) :
    finrank K H + 5 ≤ 3 * Fintype.card S := by
  let f := pairCrossMap A B
  let g := rectangularTraceDual (K := K) (S := S)
  have hm : (g.comp f).range ≤ H.dualAnnihilator := by
    rintro _ ⟨X, rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro M hM
    change trace (M * (A * crossMatrix (fun i ↦ X i 0) + B * crossMatrix (fun i ↦ X i 1))) = 0
    rw [Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      trace_mul_crossMatrix_eq_zero_of_isSymm _ (hA M hM),
      trace_mul_crossMatrix_eq_zero_of_isSymm _ (hB M hM)]
    simp
  have hd : finrank K (g.comp f).range = finrank K f.range := by
    rw [LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective g rectangularTraceDual_injective f.range).finrank_eq.symm
  have hr := Submodule.finrank_mono hm
  rw [hd] at hr
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq H
  have hker := finrank_pairCrossMap_ker_le_one A B hk hab
  change finrank K f.ker ≤ 1 at hker
  have hf := f.finrank_range_add_finrank_ker
  have h6 : finrank K (Matrix (Fin 3) (Fin 2) K) = 6 := by simp [Module.finrank_matrix]
  have hdim : finrank K (Matrix (Fin 3) S K) = 3 * Fintype.card S := by simp [Module.finrank_matrix]
  rw [hdim] at hsum
  rw [h6] at hf
  omega

end MMRank
