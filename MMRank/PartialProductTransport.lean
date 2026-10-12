module

public import MMRank.PartialTwoByTwo
public import MMRank.TwoByTwoNormalForm

@[expose] public section

/-! # Нижняя оценка для произвольных трёх независимых выходов произведения 2×n на n×2 -/

namespace MMRank
open Matrix Module
variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

/-- Две строки как прямоугольная матрица. -/
def pairRows : ((N → K) × (N → K)) →ₗ[K] Matrix (Fin 2) N K where
  toFun x := ![x.1, x.2]
  map_add' := by intro x y; ext i j; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i j; fin_cases i <;> rfl

/-- Два столбца как прямоугольная матрица. -/
def pairCols : ((N → K) × (N → K)) →ₗ[K] Matrix N (Fin 2) K where
  toFun x := (pairRows x).transpose
  map_add' := by intros; simp
  map_smul' := by intros; simp

omit [Fintype N] in
@[simp] theorem pairRows_apply (x : (N → K) × (N → K)) : pairRows x = ![x.1, x.2] := rfl

omit [Fintype N] in
@[simp] theorem pairCols_apply (x : (N → K) × (N → K)) :
    pairCols x = Matrix.transpose ![x.1, x.2] := rfl

theorem pairRows_mul_pairCols (x y : (N → K) × (N → K)) :
    pairRows x * pairCols y = !![x.1 ⬝ᵥ y.1, x.1 ⬝ᵥ y.2; x.2 ⬝ᵥ y.1, x.2 ⬝ᵥ y.2] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Контрагредиентные изменения входов и теста сохраняют скалярную свёртку.
Все три физических размера произвольны. -/
theorem trace_product_transport {P S : Type*} [Fintype P] [Fintype S]
    [DecidableEq P] [DecidableEq S]
    (L : (Matrix S S K)ˣ) (R : (Matrix P P K)ˣ) (C : Matrix P S K)
    (A : Matrix S N K) (B : Matrix N P K) :
    trace (((↑R : Matrix P P K) * C * (↑L : Matrix S S K)) *
      (((↑(L⁻¹) : Matrix S S K) * A) * (B * (↑(R⁻¹) : Matrix P P K)))) =
      trace (C * (A * B)) := by
  have he : ((↑R : Matrix P P K) * C * (↑L : Matrix S S K)) *
      (((↑(L⁻¹) : Matrix S S K) * A) * (B * (↑(R⁻¹) : Matrix P P K))) =
      (↑R : Matrix P P K) * ((C * (A * B)) * (↑(R⁻¹) : Matrix P P K)) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑L : Matrix S S K), Units.mul_inv, Matrix.one_mul]
  rw [he, trace_mul_comm, Matrix.mul_assoc, Units.inv_mul, mul_one]

/-- Независимость трёх выходов задана размерностью пространства тестов.
Любая точная формула на этих тестах имеет длину≥3n, над произвольным полем.
Коэффициенты c_i(C) могут быть произвольными функциями: их линейность
для этой нижней оценки не нужна. -/
theorem partial_twoByTwo_lower
    (T : Submodule K (Matrix (Fin 2) (Fin 2) K)) (hT : finrank K T = 3)
    (a : I → Matrix (Fin 2) N K →ₗ[K] K) (b : I → Matrix N (Fin 2) K →ₗ[K] K)
    (c : I → Matrix (Fin 2) (Fin 2) K → K)
    (h : ∀ C ∈ T, ∀ A B, trace (C * (A * B)) = ∑ i, (a i A * b i B) * c i C) :
    3 * Fintype.card N ≤ Fintype.card I := by
  classical
  obtain ⟨M, hM, hker⟩ := exists_twoByTwo_trace_normal T hT
  obtain ⟨L, R, hnorm⟩ := twoByTwo_nonzero_normal_form M hM
  let test := fun C : Matrix (Fin 2) (Fin 2) K ↦
    (↑R : Matrix (Fin 2) (Fin 2) K) * C * (↑L : Matrix (Fin 2) (Fin 2) K)
  let ain := mulLeftLinearMap N K (↑(L⁻¹) : Matrix (Fin 2) (Fin 2) K)
  let bin := mulRightLinearMap N K (↑(R⁻¹) : Matrix (Fin 2) (Fin 2) K)
  have htest (C : Matrix (Fin 2) (Fin 2) K)
      (hc : trace (C * ((↑L : Matrix (Fin 2) (Fin 2) K) * M *
        (↑R : Matrix (Fin 2) (Fin 2) K))) = 0) : test C ∈ T := by
    rw [hker]
    change trace (((↑R : Matrix (Fin 2) (Fin 2) K) * C * (↑L : Matrix (Fin 2) (Fin 2) K)) * M) = 0
    calc
      trace (((↑R : Matrix (Fin 2) (Fin 2) K) * C * (↑L : Matrix (Fin 2) (Fin 2) K)) * M) =
          trace ((↑R : Matrix (Fin 2) (Fin 2) K) * (C * ((↑L : Matrix (Fin 2) (Fin 2) K) * M))) := by
            simp only [Matrix.mul_assoc]
      _ = trace ((C * ((↑L : Matrix (Fin 2) (Fin 2) K) * M)) *
          (↑R : Matrix (Fin 2) (Fin 2) K)) := trace_mul_comm _ _
      _ = 0 := by simpa only [Matrix.mul_assoc] using hc
  have hform (C : Matrix (Fin 2) (Fin 2) K) (hc : test C ∈ T)
      (A : Matrix (Fin 2) N K) (B : Matrix N (Fin 2) K) :
      trace (C * (A * B)) = ∑ i, (a i (ain A) * b i (bin B)) * c i (test C) := by
    rw [← trace_product_transport L R C A B]
    exact h (test C) hc (ain A) (bin B)
  rcases hnorm with hn | hn
  · let t : Fin 3 → Matrix (Fin 2) (Fin 2) K :=
      ![single 1 1 1, single 0 1 1, single 1 0 1]
    let swap := LinearEquiv.prodComm K (N → K) (N → K)
    let aa := fun i ↦ (a i).comp (ain.comp (pairRows.comp swap.toLinearMap))
    let bb := fun i ↦ (b i).comp (bin.comp (pairCols.comp swap.toLinearMap))
    apply partial_twoByTwo_singular_lower aa bb (fun i k ↦ c i (test (t k)))
    intro x y u v
    funext k
    have ht : test (t k) ∈ T := htest (t k) (by
      rw [hn]; fin_cases k <;> simp [t])
    have hh := hform (t k) ht (pairRows (y, x)) (pairCols (v, u))
    rw [pairRows_mul_pairCols] at hh
    fin_cases k <;>
      simpa [aa, bb, swap, t, trace_single_mul, Matrix.mul_apply,
        dotProduct, Finset.sum_apply] using hh
  · let t : Fin 3 → Matrix (Fin 2) (Fin 2) K :=
      ![single 0 0 1 - single 1 1 1, single 1 0 1, single 0 1 1]
    let aa := fun i ↦ (a i).comp (ain.comp pairRows)
    let bb := fun i ↦ (b i).comp (bin.comp pairCols)
    apply partial_twoByTwo_nonsingular_lower aa bb (fun i k ↦ c i (test (t k)))
    intro x y u v
    funext k
    have ht : test (t k) ∈ T := htest (t k) (by
      rw [hn]; fin_cases k <;> simp [t, Matrix.trace, Fin.sum_univ_two])
    have hh := hform (t k) ht (pairRows (x, y)) (pairCols (u, v))
    rw [pairRows_mul_pairCols] at hh
    fin_cases k <;>
      simpa [aa, bb, t, sub_mul, trace_sub, trace_single_mul,
        Matrix.mul_apply, dotProduct, Finset.sum_apply] using hh

end MMRank
