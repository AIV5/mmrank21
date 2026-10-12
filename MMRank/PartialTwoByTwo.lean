module

public import MMRank.ThreeSliceFlattening
public import MMRank.LinearSubstitution
public import Mathlib.LinearAlgebra.Matrix.Dual

@[expose] public section

/-! # Три выхода произведения 2×n на n×2: обе нормальные формы -/

namespace MMRank
open Matrix Module
variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

/-- Две строки с их естественным невырожденным скалярным спариванием. -/
noncomputable def pairDotEquiv [DecidableEq N] :
    ((N → K) × (N → K)) ≃ₗ[K] Module.Dual K ((N → K) × (N → K)) :=
  ((dotProductEquiv K N).prodCongr (dotProductEquiv K N)).trans
    (Module.dualProdDualEquivDual K (N → K) (N → K))

@[simp] theorem pairDotEquiv_apply [DecidableEq N]
    (x y : (N → K) × (N → K)) :
    pairDotEquiv x y = x.1 ⬝ᵥ y.1 + x.2 ⬝ᵥ y.2 := rfl

/-- Обратимый диагональный срез; знак сохраняет корректность в характеристике2. -/
def pairSignEquiv {V : Type*} [AddCommGroup V] [Module K V] : (V × V) ≃ₗ[K] (V × V) where
  toFun x := (x.1, -x.2)
  invFun x := (x.1, -x.2)
  map_add' := by intros; ext <;> simp [add_comm]
  map_smul' := by intros; ext <;> simp
  left_inv := by intro x; simp
  right_inv := by intro x; simp

def pairUpper {V : Type*} [AddCommGroup V] [Module K V] : (V × V) →ₗ[K] (V × V) :=
  (LinearMap.snd K V V).prod 0

def pairLower {V : Type*} [AddCommGroup V] [Module K V] : (V × V) →ₗ[K] (V × V) :=
  (0 : (V × V) →ₗ[K] V).prod (LinearMap.fst K V V)

/-- Коммутатор срезов равен единице; деления на2 нет. -/
theorem pair_slices_commutator {V : Type*} [AddCommGroup V] [Module K V] :
    (pairLower : (V × V) →ₗ[K] (V × V)).comp (pairSignEquiv.symm.toLinearMap.comp pairUpper) -
      pairUpper.comp (pairSignEquiv.symm.toLinearMap.comp pairLower) = LinearMap.id := by
  apply LinearMap.ext; intro x
  ext <;> simp [pairLower, pairUpper, pairSignEquiv]

/-- Нормаль ранга два: любые первые/вторые формы, вычисляющие
x·u−y·v, x·v, y·u, требуют не меньше3n членов. -/
theorem partial_twoByTwo_nonsingular_lower
    (a b : I → ((N → K) × (N → K)) →ₗ[K] K) (c : I → Fin 3 → K)
    (h : ∀ x y u v : N → K,
      ![x ⬝ᵥ u - y ⬝ᵥ v, x ⬝ᵥ v, y ⬝ᵥ u] =
        ∑ i, (a i (x, y) * b i (u, v)) • c i) :
    3 * Fintype.card N ≤ Fintype.card I := by
  classical
  let V := (N → K) × (N → K)
  let w : I → V := fun i ↦ pairDotEquiv.symm (a i)
  have hw (i : I) (z : V) : pairDotEquiv (w i) z = a i z :=
    DFunLike.congr_fun (pairDotEquiv.apply_symm_apply (a i)) z
  have hslices :
      (pairSignEquiv : V ≃ₗ[K] V).toLinearMap = ∑ i, c i 0 • (b i).smulRight (w i) ∧
      (pairUpper : V →ₗ[K] V) = ∑ i, c i 1 • (b i).smulRight (w i) ∧
      (pairLower : V →ₗ[K] V) = ∑ i, c i 2 • (b i).smulRight (w i) := by
    have aux (k : Fin 3) :
        (![pairSignEquiv.toLinearMap, pairUpper, pairLower] k : V →ₗ[K] V) =
          ∑ i, c i k • (b i).smulRight (w i) := by
      apply LinearMap.ext; rintro ⟨u, v⟩
      apply pairDotEquiv.injective
      apply LinearMap.ext; rintro ⟨x, y⟩
      have hh := congrFun (h x y u v) k
      have hr : pairDotEquiv ((∑ i, c i k • (b i).smulRight (w i)) (u, v)) (x, y) =
          ∑ i, (a i (x, y) * b i (u, v)) * c i k := by
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
          map_sum, map_smul, hw, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _; ring
      rw [hr]
      fin_cases k <;>
        simpa [pairDotEquiv_apply, pairSignEquiv, pairUpper, pairLower, dotProduct_comm,
          Finset.sum_apply, sub_eq_add_neg] using hh
    exact ⟨aux 0, aux 1, aux 2⟩
  have hi : Function.Injective (threeSliceLinear
      (pairSignEquiv : V ≃ₗ[K] V).toLinearMap pairUpper pairLower) :=
    threeSlice_injective_of_commutator (pairSignEquiv (K := K) (V := N → K)) pairUpper pairLower
      (by rw [pair_slices_commutator]; exact Function.injective_id)
  have hd := LinearMap.finrank_range_of_inj hi
  have hb := threeSlice_rank_le_twice_length b w (fun i ↦ c i 0) (fun i ↦ c i 1) (fun i ↦ c i 2)
  rw [← hslices.1, ← hslices.2.1, ← hslices.2.2, hd] at hb
  have hdim : finrank K (Fin 3 → V) = 6 * Fintype.card N := by
    simp [V, Module.finrank_pi_fintype, Module.finrank_prod, Nat.mul_add]
    omega
  rw [hdim] at hb
  omega

/-- Нормаль ранга один: x·u, x·v, y·u требуют не меньше3n членов. -/
theorem partial_twoByTwo_singular_lower
    (a b : I → ((N → K) × (N → K)) →ₗ[K] K) (c : I → Fin 3 → K)
    (h : ∀ x y u v : N → K,
      ![x ⬝ᵥ u, x ⬝ᵥ v, y ⬝ᵥ u] = ∑ i, (a i (x, y) * b i (u, v)) • c i) :
    3 * Fintype.card N ≤ Fintype.card I := by
  classical
  have ha : ∀ y : N → K, (∀ i, a i (0, y) = 0) → y = 0 := by
    intro y hy
    ext j
    have hh := congrFun (h 0 y (Pi.single j 1) 0) 2
    simpa [hy, Finset.sum_apply] using hh
  have hf (x y : N → K) (v : (N → K) × (N → K)) :
      (x ⬝ᵥ v.1, x ⬝ᵥ v.2) = ∑ i, (a i (x, y) * b i v) • (c i 0, c i 1) := by
    have h0 := congrFun (h x y v.1 v.2) 0
    have h1 := congrFun (h x y v.1 v.2) 1
    apply Prod.ext
    · simpa [Finset.sum_apply, Prod.fst_sum] using h0
    · simpa [Finset.sum_apply, Prod.snd_sum] using h1
  have hsep (v : (N → K) × (N → K))
      (hv : ∀ x, (x ⬝ᵥ v.1, x ⬝ᵥ v.2) = (0 : K × K)) : v = 0 := by
    apply Prod.ext <;> ext j
    · have hh := congrArg Prod.fst (hv (Pi.single j 1)); simpa using hh
    · have hh := congrArg Prod.snd (hv (Pi.single j 1)); simpa using hh
  have hb := bilinear_length_bound_of_substitution a b (fun i ↦ (c i 0, c i 1))
    (fun x v ↦ (x ⬝ᵥ v.1, x ⬝ᵥ v.2)) ha hf hsep
  simp only [Module.finrank_prod, Module.finrank_pi] at hb
  omega

end MMRank
