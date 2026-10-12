import MMRank.BasisFrameMatrices
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Пятиэлементный rank1-базис критического аннулятора333

Пять разностей вдоль пути12,13,23,21,31,32 вместо классификации
простого локуса и вычисления миноров. Поле произвольно.
-/
noncomputable section
namespace MMRank.CriticalThreeAnnihilator
open Matrix Module
variable {K : Type*} [Field K]

/-- Нулевая диагональ и аннуляция четвёртого простого теста. -/
def weightedSpace (a b : Fin 3 → K) : Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := {T | (∀ i, T i i = 0) ∧ trace (T * vecMulVec a b) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro T S hT hS
    exact ⟨fun i ↦ by simp [hT.1 i, hS.1 i], by
      simp [Matrix.add_mul, hT.2, hS.2]⟩
  smul_mem' := by
    intro c T hT
    exact ⟨fun i ↦ by simp [hT.1 i], by simp [hT.2]⟩

/-- Обратная координатная карта: взвешенные записи образуют разности. -/
def decode (a b : Fin 3 → K) (c : Fin 5 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, c 0 / (b 0 * a 1), (c 1 - c 0) / (b 0 * a 2);
     (c 3 - c 2) / (b 1 * a 0), 0, (c 2 - c 1) / (b 1 * a 2);
     (c 4 - c 3) / (b 2 * a 0), -c 4 / (b 2 * a 1), 0]

/-- Координаты по пяти разностям — последовательные суммы записей пути. -/
def encode (a b : Fin 3 → K) (T : Matrix (Fin 3) (Fin 3) K) : Fin 5 → K :=
  let y₀ := b 0 * T 0 1 * a 1
  let y₁ := b 0 * T 0 2 * a 2
  let y₂ := b 1 * T 1 2 * a 2
  let y₃ := b 1 * T 1 0 * a 0
  let y₄ := b 2 * T 2 0 * a 0
  ![y₀, y₀ + y₁, y₀ + y₁ + y₂, y₀ + y₁ + y₂ + y₃,
    y₀ + y₁ + y₂ + y₃ + y₄]

private theorem trace_weighted (a b : Fin 3 → K) (T : Matrix (Fin 3) (Fin 3) K) :
    trace (T * vecMulVec a b) =
      b 0 * T 0 0 * a 0 + b 0 * T 0 1 * a 1 + b 0 * T 0 2 * a 2 +
      b 1 * T 1 0 * a 0 + b 1 * T 1 1 * a 1 + b 1 * T 1 2 * a 2 +
      b 2 * T 2 0 * a 0 + b 2 * T 2 1 * a 1 + b 2 * T 2 2 * a 2 := by
  simp [Matrix.trace, Matrix.mul_apply, vecMulVec, Fin.sum_univ_succ]
  ring

private theorem decode_mem (a b : Fin 3 → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (c : Fin 5 → K) :
    decode a b c ∈ weightedSpace a b := by
  constructor
  · intro i; fin_cases i <;> simp [decode]
  · rw [trace_weighted]
    simp [decode]
    field_simp [ha, hb]
    ring

private theorem encode_decode (a b : Fin 3 → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (c : Fin 5 → K) :
    encode a b (decode a b c) = c := by
  ext i; fin_cases i <;> simp [encode, decode] <;> field_simp [ha, hb] <;> ring

private theorem decode_encode (a b : Fin 3 → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (T : weightedSpace a b) : decode a b (encode a b T.val) = T.val := by
  have htrace := T.property.2
  rw [trace_weighted] at htrace
  have hdiag := T.property.1
  simp only [hdiag, mul_zero, zero_mul, zero_add, add_zero] at htrace
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [decode, encode, hdiag] <;> (field_simp [ha, hb]; try ring1)
  linear_combination -htrace

/-- Явные координаты аннулятора: независимость и порождение одним тождеством. -/
def coordinateEquiv (a b : Fin 3 → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    weightedSpace a b ≃ₗ[K] (Fin 5 → K) where
  toFun T := encode a b T.val
  invFun c := ⟨decode a b c, decode_mem a b ha hb c⟩
  left_inv T := Subtype.ext (decode_encode a b ha hb T)
  right_inv c := encode_decode a b ha hb c
  map_add' := by
    intro T S; ext i; fin_cases i <;> simp [encode] <;> ring
  map_smul' := by
    intro c T; ext i; fin_cases i <;> simp [encode] <;> ring

/-- Базис из пяти соседних разностей взвешенных матричных единиц. -/
def pathBasis (a b : Fin 3 → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    Basis (Fin 5) K (weightedSpace a b) :=
  Basis.ofEquivFun (coordinateEquiv a b ha hb)

private def leftFactor (a b : Fin 3 → K) : Fin 5 → Fin 3 → K :=
  ![![1, 0, 0], ![(b 0 * a 2)⁻¹, -(b 1 * a 2)⁻¹, 0], ![0, 1, 0],
    ![0, (b 1 * a 0)⁻¹, -(b 2 * a 0)⁻¹], ![0, 0, 1]]

private def rightFactor (a b : Fin 3 → K) : Fin 5 → Fin 3 → K :=
  ![![0, (b 0 * a 1)⁻¹, -(b 0 * a 2)⁻¹], ![0, 0, 1],
    ![-(b 1 * a 0)⁻¹, 0, (b 1 * a 2)⁻¹], ![1, 0, 0],
    ![(b 2 * a 0)⁻¹, -(b 2 * a 1)⁻¹, 0]]

private theorem decode_single (a b : Fin 3 → K) (i : Fin 5) :
    decode a b (Pi.single i 1) = vecMulVec (leftFactor a b i) (rightFactor a b i) := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [decode, leftFactor, rightFactor, vecMulVec, div_eq_mul_inv]

@[simp] theorem pathBasis_apply (a b : Fin 3 → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (i : Fin 5) :
    (pathBasis a b ha hb i).val = decode a b (Pi.single i 1) := by
  rw [pathBasis, Basis.coe_ofEquivFun]
  rfl

/-- Все пять базисных матриц имеют ранг ровно1. -/
theorem pathBasis_rank_one (a b : Fin 3 → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (i : Fin 5) :
    (pathBasis a b ha hb i).val.rank = 1 := by
  rw [pathBasis_apply]
  have hr : (decode a b (Pi.single i 1)).rank ≤ 1 := by
    rw [decode_single]
    exact rank_vecMulVec_le _ _
  have hn : decode a b (Pi.single i 1) ≠ 0 := by
    intro hz
    have hh := congrFun (encode_decode a b ha hb (Pi.single i 1)) i
    rw [hz] at hh
    fin_cases i <;> simp [encode] at hh
  have hn' := (matrix_rank_eq_zero_iff _).not.mpr hn
  omega

private def frameCoordinates (A B : (Matrix (Fin 3) (Fin 3) K)ˣ) :
    Matrix (Fin 3) (Fin 3) K ≃ₗ[K] Matrix (Fin 3) (Fin 3) K :=
  (transposeLinearEquiv (Fin 3) (Fin 3) K K).trans
    ((A.mulLeftLinearEquiv K _).trans
      ((transposeLinearEquiv (Fin 3) (Fin 3) K K).trans (B.mulLeftLinearEquiv K _)))

private theorem frameCoordinates_apply (A B : (Matrix (Fin 3) (Fin 3) K)ˣ)
    (T : Matrix (Fin 3) (Fin 3) K) :
    frameCoordinates A B T = (B : Matrix (Fin 3) (Fin 3) K) * T *
      (A : Matrix (Fin 3) (Fin 3) K)ᵀ := by
  simp [frameCoordinates, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem frameCoordinates_rank (A B : (Matrix (Fin 3) (Fin 3) K)ˣ)
    (T : Matrix (Fin 3) (Fin 3) K) : (frameCoordinates A B T).rank = T.rank := by
  rw [frameCoordinates_apply,
    rank_mul_eq_left_of_isUnit_det _ _ (by simpa using Matrix.isUnits_det_units A),
    rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units B)]

private theorem trace_frameCoordinates (A B : (Matrix (Fin 3) (Fin 3) K)ˣ)
    (T C : Matrix (Fin 3) (Fin 3) K) :
    trace (T * ((A : Matrix (Fin 3) (Fin 3) K)ᵀ * C *
      (B : Matrix (Fin 3) (Fin 3) K))) = trace (frameCoordinates A B T * C) := by
  rw [frameCoordinates_apply]
  simpa only [Matrix.mul_assoc] using
    trace_mul_comm (T * (A : Matrix (Fin 3) (Fin 3) K)ᵀ * C)
      (B : Matrix (Fin 3) (Fin 3) K)

/-- Любой аннулятор четырёх тестов с двумя проективными реперами имеет
пятиэлементный rank1-базис. Точность алгоритма и бесконечность поля не нужны. -/
theorem exists_frame_annihilator_basis
    (R : Submodule K (Matrix (Fin 3) (Fin 3) K)) (x y : Fin 4 → Fin 3 → K)
    (hR : ∀ T, T ∈ R ↔ ∀ j, trace (T * vecMulVec (x j) (y j)) = 0)
    (hx : ∀ e : Fin 3 → Fin 4, Function.Injective e → LinearIndependent K (x ∘ e))
    (hy : ∀ e : Fin 3 → Fin 4, Function.Injective e → LinearIndependent K (y ∘ e)) :
    ∃ c : Basis (Fin 5) K R, ∀ i, (c i).val.rank = 1 := by
  classical
  obtain ⟨p, hp, ha⟩ := exists_basis_of_projective_frame 3 (by simp) x hx
  obtain ⟨s, hs, hb⟩ := exists_basis_of_projective_frame 3 (by simp) y hy
  let a : Fin 3 → K := fun i ↦ p.repr (x 3) i
  let b : Fin 3 → K := fun i ↦ s.repr (y 3) i
  let A := basisRowUnit p
  let B := basisRowUnit s
  let e := frameCoordinates A B
  have ha' : ∀ i, a i ≠ 0 := ha
  have hb' : ∀ i, b i ≠ 0 := hb
  have hd (T : Matrix (Fin 3) (Fin 3) K) (j : Fin 3) :
      trace (T * vecMulVec (x j.castSucc) (y j.castSucc)) = e T j j := by
    rw [← hp j, ← hs j, ← basis_frame_single p s j]
    rw [trace_frameCoordinates, trace_mul_single]
    simp [e, A, B]
  have hf (T : Matrix (Fin 3) (Fin 3) K) :
      trace (T * vecMulVec (x 3) (y 3)) = trace (e T * vecMulVec a b) := by
    rw [← basis_frame_test p s (x 3) (y 3)]
    exact trace_frameCoordinates A B T (vecMulVec a b)
  have heq : R = (weightedSpace a b).comap e.toLinearMap := by
    ext T
    rw [hR]
    change (∀ j, trace (T * vecMulVec (x j) (y j)) = 0) ↔
      (∀ i, e T i i = 0) ∧ trace (e T * vecMulVec a b) = 0
    constructor
    · intro h
      exact ⟨fun i ↦ (hd T i).symm.trans (h i.castSucc), (hf T).symm.trans (h 3)⟩
    · rintro ⟨hdiag, hsum⟩ j
      fin_cases j
      · exact (hd T 0).trans (hdiag 0)
      · exact (hd T 1).trans (hdiag 1)
      · exact (hd T 2).trans (hdiag 2)
      · exact (hf T).trans hsum
  let f : R ≃ₗ[K] weightedSpace a b :=
    (LinearEquiv.ofEq _ _ heq).trans (e.ofSubmodule' (weightedSpace a b))
  let c := (pathBasis a b ha' hb').map f.symm
  refine ⟨c, ?_⟩
  intro i
  have hc : (c i).val = e.symm (pathBasis a b ha' hb' i).val := by
    simp [c, f]
  rw [hc]
  have hr := frameCoordinates_rank A B (e.symm (pathBasis a b ha' hb' i).val)
  change (e (e.symm _)).rank = _ at hr
  rw [e.apply_symm_apply] at hr
  exact hr.symm.trans (pathBasis_rank_one a b ha' hb' i)

end MMRank.CriticalThreeAnnihilator
