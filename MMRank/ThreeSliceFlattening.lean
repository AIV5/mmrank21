module

public import MMRank.PairSliceFlattening

@[expose] public section

/-! # Трёхсрезовая линейная развёртка над произвольным полем -/

namespace MMRank
open Module
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Блочное отображение (x,y,z)↦(Sy−Qz,Pz−Sx,Qx−Py).
Это вспомогательная развёртка; соглашение о физических строках не меняется. -/
def threeSliceLinear (P Q S : V →ₗ[K] W) : (Fin 3 → V) →ₗ[K] (Fin 3 → W) :=
  LinearMap.pi ![S.comp (LinearMap.proj 1) - Q.comp (LinearMap.proj 2),
    P.comp (LinearMap.proj 2) - S.comp (LinearMap.proj 0),
    Q.comp (LinearMap.proj 0) - P.comp (LinearMap.proj 1)]

@[simp] theorem threeSliceLinear_apply (P Q S : V →ₗ[K] W) (x : Fin 3 → V) :
    threeSliceLinear P Q S x = ![S (x 1) - Q (x 2), P (x 2) - S (x 0), Q (x 0) - P (x 1)] := by
  ext i; fin_cases i <;> rfl

/-- Скалярная альтернированная матрица имеет ранг≤2 во всех характеристиках. -/
theorem scalar_threeSlice_rank_le_two (p q s : K) :
    finrank K (threeSliceLinear (p • (LinearMap.id : K →ₗ[K] K))
      (q • LinearMap.id) (s • LinearMap.id)).range ≤ 2 := by
  let f := pairSliceLinear (fun i : Fin 3 ↦ (![p, q, s] : Fin 3 → K) i •
    (LinearMap.id : K →ₗ[K] K))
  let entry (i j : Fin 3) : (Fin 3 → Fin 3 → K) →ₗ[K] K :=
    (LinearMap.proj j : (Fin 3 → K) →ₗ[K] K).comp
      (LinearMap.proj i : (Fin 3 → Fin 3 → K) →ₗ[K] (Fin 3 → K))
  let b : (Fin 3 → Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    LinearMap.pi ![entry 2 1, entry 0 2, entry 1 0]
  have he : (b.comp f.range.subtype).comp f.rangeRestrict =
      threeSliceLinear (p • (LinearMap.id : K →ₗ[K] K))
        (q • LinearMap.id) (s • LinearMap.id) := by
    apply LinearMap.ext; intro x; funext i
    fin_cases i <;> rfl
  have hb := finrank_range_le_of_factorization f.rangeRestrict (b.comp f.range.subtype)
  rw [he] at hb
  exact hb.trans (by simpa [f] using scalar_pairSlice_rank_le (![p, q, s] : Fin 3 → K))

/-- Один простой билинейный член в трёхсрезовой развёртке имеет ранг≤2.
Конечномерность исходного и выходного пространств не требуется. -/
theorem simple_threeSlice_rank_le_two (a : V →ₗ[K] K) (w : W) (p q s : K) :
    finrank K (threeSliceLinear (p • a.smulRight w) (q • a.smulRight w)
      (s • a.smulRight w)).range ≤ 2 := by
  let f := threeSliceLinear (p • (LinearMap.id : K →ₗ[K] K)) (q • LinearMap.id) (s • LinearMap.id)
  let A : (Fin 3 → V) →ₗ[K] (Fin 3 → K) := LinearMap.pi (fun i ↦ a.comp (LinearMap.proj i))
  let B : (Fin 3 → K) →ₗ[K] (Fin 3 → W) :=
    LinearMap.pi (fun i ↦ (LinearMap.proj i).smulRight w)
  have he : (B.comp f.range.subtype).comp (f.rangeRestrict.comp A) =
      threeSliceLinear (p • a.smulRight w) (q • a.smulRight w) (s • a.smulRight w) := by
    apply LinearMap.ext; intro x; funext i
    fin_cases i <;> simp [A, B, f, threeSliceLinear, sub_smul, smul_smul]
  have hh := finrank_range_le_of_factorization (f.rangeRestrict.comp A) (B.comp f.range.subtype)
  rw [he] at hh
  exact hh.trans (scalar_threeSlice_rank_le_two p q s)

/-- Развёртка линейна по тройке срезов. -/
theorem threeSliceLinear_sum {I : Type*} [Fintype I] (P Q S : I → V →ₗ[K] W) :
    threeSliceLinear (∑ i, P i) (∑ i, Q i) (∑ i, S i) =
      ∑ i, threeSliceLinear (P i) (Q i) (S i) := by
  apply LinearMap.ext; intro x; funext j
  fin_cases j <;> simp [threeSliceLinear, LinearMap.sum_apply, Finset.sum_sub_distrib]

/-- Общая нижняя оценка длины через ранг трёхсрезовой развёртки.
Никакой нормальной формы или обратимости отдельного среза не требуется. -/
theorem threeSlice_rank_le_twice_length [FiniteDimensional K V] {I : Type*} [Fintype I]
    (a : I → V →ₗ[K] K) (w : I → W) (p q s : I → K) :
    finrank K (threeSliceLinear (∑ i, p i • (a i).smulRight (w i))
      (∑ i, q i • (a i).smulRight (w i)) (∑ i, s i • (a i).smulRight (w i))).range ≤
      2 * Fintype.card I := by
  rw [threeSliceLinear_sum]
  have hh := finrank_range_sum_le (fun i ↦ threeSliceLinear
    (p i • (a i).smulRight (w i)) (q i • (a i).smulRight (w i)) (s i • (a i).smulRight (w i)))
  exact hh.trans (by
    calc
      _ ≤ ∑ i : I, 2 := Finset.sum_le_sum (fun i _ ↦ simple_threeSlice_rank_le_two (a i) (w i) _ _ _)
      _ = 2 * Fintype.card I := by simp [Nat.mul_comm])

/-- Обратимый первый срез и инъективный коммутатор обеспечивают
инъективность всей развёртки; конечномерность не нужна. -/
theorem threeSlice_injective_of_commutator (P : V ≃ₗ[K] V) (Q S : V →ₗ[K] V)
    (h : Function.Injective (S.comp (P.symm.toLinearMap.comp Q) -
      Q.comp (P.symm.toLinearMap.comp S))) :
    Function.Injective (threeSliceLinear P.toLinearMap Q S) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  simp only [threeSliceLinear_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Pi.zero_apply, LinearEquiv.coe_coe, sub_eq_zero] at h0 h1 h2
  have hy : x 1 = P.symm (Q (x 0)) := by
    apply P.injective
    simpa using h2.symm
  have hz : x 2 = P.symm (S (x 0)) := by
    apply P.injective
    simpa using h1
  have hx0 : x 0 = 0 := by
    apply h
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      map_zero]
    exact sub_eq_zero.mpr (by simpa only [hy, hz] using h0)
  ext i; fin_cases i <;> simp [hx0, hy, hz]

end MMRank
