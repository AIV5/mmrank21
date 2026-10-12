module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import MMRank.RankOneHyperplanes
public import MMRank.ThreeRayGeometry
public import MMRank.QuadraticHyperplane

@[expose] public section

/-! # Шесть квадратичных координат и сепараторы трёх лучей

Поле произвольно;
полиномы и проективные фактор-пространства не используются.
-/

namespace MMRank
open Module Matrix
open scoped BigOperators

section SeparatingForms
variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype J]

omit [Fintype J] in
/-- Диагональные ненулевые оценки отделяющих форм доказывают независимость. -/
theorem linearIndependent_of_separating_forms (v : J → V) (φ : J → Dual K V)
    (hz : ∀ i j, j ≠ i → φ i (v j) = 0) (hn : ∀ i, φ i (v i) ≠ 0) :
    LinearIndependent K v := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one v
    (fun i ↦ (φ i (v i))⁻¹ • φ i)
  · intro i j hij
    simp [hz i j hij.symm]
  · intro i
    simp [hn i]

/-- Два независимых вектора разделяются линейной формой. -/
theorem exists_dual_separating_pair (x y : V)
    (h : LinearIndependent K ![x, y]) :
    ∃ φ : Dual K V, φ x ≠ 0 ∧ φ y = 0 := by
  have hx : x ∉ Submodule.span K {y} := by
    simpa using h.notMem_span_image (s := ({1} : Set (Fin 2))) (x := 0) (by decide)
  obtain ⟨φ, hφ, hzero⟩ := (Submodule.span K {y}).exists_dual_map_eq_bot_of_notMem
    hx inferInstance
  refine ⟨φ, hφ, ?_⟩
  have hy : φ y ∈ (Submodule.span K {y}).map φ :=
    Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_singleton y))
  simpa [hzero] using hy
end SeparatingForms

section Coordinates
variable {K : Type*} [Field K]

/-- Однородные квадратичные координаты, без деления на2. -/
def quadraticVeronese (x : Fin 3 → K) : Fin 6 → K :=
  ![x 0 * x 0, x 0 * x 1, x 1 * x 1, x 0 * x 2, x 2 * x 2, x 1 * x 2]

/-- Коэффициенты произведения двух линейных форм в шести координатах. -/
def quadraticProductCoefficients (a b : Fin 3 → K) : Fin 6 → K :=
  ![a 0 * b 0, a 0 * b 1 + a 1 * b 0, a 1 * b 1,
    a 0 * b 2 + a 2 * b 0, a 2 * b 2, a 1 * b 2 + a 2 * b 1]

theorem quadraticProductCoefficients_dot (a b x : Fin 3 → K) :
    quadraticProductCoefficients a b ⬝ᵥ quadraticVeronese x =
      (a ⬝ᵥ x) * (b ⬝ᵥ x) := by
  simp [quadraticProductCoefficients, quadraticVeronese, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- Произведение двух форм представляется обычной формой на K⁶. -/
theorem exists_quadratic_product_form (α β : Dual K (Fin 3 → K)) :
    ∃ ell : Dual K (Fin 6 → K), ∀ x,
      ell (quadraticVeronese x) = α x * β x := by
  let a := (dotProductEquiv K (Fin 3)).symm α
  let b := (dotProductEquiv K (Fin 3)).symm β
  refine ⟨dotProductEquiv K (Fin 6) (quadraticProductCoefficients a b), ?_⟩
  intro x
  have ha : a ⬝ᵥ x = α x :=
    DFunLike.congr_fun ((dotProductEquiv K (Fin 3)).apply_symm_apply α) x
  have hb : b ⬝ᵥ x = β x :=
    DFunLike.congr_fun ((dotProductEquiv K (Fin 3)).apply_symm_apply β) x
  exact (quadraticProductCoefficients_dot a b x).trans (by rw [ha, hb])

/-- Три разные ненулевые линии налагают независимые квадратичные условия. -/
theorem quadraticCoordinates_three_linearIndependent (x : Fin 3 → Fin 3 → K)
    (hx : Pairwise fun i j => LinearIndependent K ![x i, x j]) :
    LinearIndependent K (fun i => quadraticVeronese (x i)) := by
  have hsep (i : Fin 3) : ∃ ell : Dual K (Fin 6 → K),
      ell (quadraticVeronese (x i)) ≠ 0 ∧
      ∀ j, j ≠ i → ell (quadraticVeronese (x j)) = 0 := by
    have h1 : i ≠ i + 1 := by fin_cases i <;> decide
    have h2 : i ≠ i + 2 := by fin_cases i <;> decide
    obtain ⟨α, ha, hz⟩ := exists_dual_separating_pair (x i) (x (i + 1)) (hx h1)
    obtain ⟨β, hb, hw⟩ := exists_dual_separating_pair (x i) (x (i + 2)) (hx h2)
    obtain ⟨ell, hell⟩ := exists_quadratic_product_form α β
    refine ⟨ell, ?_, ?_⟩
    · rw [hell]
      exact mul_ne_zero ha hb
    · intro j hji
      have hj : j = i + 1 ∨ j = i + 2 := by
        fin_cases i <;> fin_cases j <;> simp_all
      rcases hj with rfl | rfl
      · simp [hell, hz]
      · simp [hell, hw]
  choose ell hn hz using hsep
  exact linearIndependent_of_separating_forms _ ell hz hn
end Coordinates

section PlaneVanishing
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Три разные линии плоскости определяют квадратичную форму на ней.
Аргумент через поляризацию действует также в характеристике2. -/
theorem quadratic_zero_on_plane_of_three (P : Submodule K V) (hP : finrank K P = 2)
    (Q : QuadraticForm K V) (x : Fin 3 → V)
    (hp : Pairwise fun i j ↦ LinearIndependent K ![x i, x j])
    (hx : ∀ i, x i ∈ P) (hq : ∀ i, Q (x i) = 0) :
    ∀ z ∈ P, Q z = 0 := by
  have hs := span_pair_eq_of_mem_plane P hP (x 0) (x 1) (hx 0) (hx 1)
    (hp (by decide))
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hs ▸ hx 2)
  have ha : a ≠ 0 := by
    intro ha
    have he : b • x 1 = x 2 := by simpa [ha] using hab
    exact (LinearIndependent.pair_iff' ((hp (by decide : (1 : Fin 3) ≠ 2)).ne_zero 0)).mp
      (hp (by decide)) b he
  have hb : b ≠ 0 := by
    intro hb
    have he : a • x 0 = x 2 := by simpa [hb] using hab
    exact (LinearIndependent.pair_iff' ((hp (by decide : (0 : Fin 3) ≠ 2)).ne_zero 0)).mp
      (hp (by decide)) a he
  have hpolar : QuadraticMap.polar Q (x 0) (x 1) = 0 := by
    have hh := hq 2
    rw [← hab, QuadraticMap.map_add Q, Q.map_smul, Q.map_smul,
      Q.polar_smul_left, Q.polar_smul_right, hq 0, hq 1] at hh
    simpa only [smul_zero, zero_add, smul_eq_mul, mul_zero, mul_eq_zero,
      ha, hb, false_or] using hh
  intro z hz
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp (hs ▸ hz)
  simp [QuadraticMap.map_add Q, Q.map_smul, Q.polar_smul_left, Q.polar_smul_right, hq, hpolar]

/-- Три нуля в первой плоскости, два внешних во второй и один вне обеих
заставляют квадратичную форму обращаться в нуль. Размерность пространства3. -/
theorem quadratic_zero_of_three_two_one [FiniteDimensional K V]
    (hV : finrank K V = 3) (P T : Submodule K V)
    (hP : finrank K P = 2) (hT : finrank K T = 2)
    (Q : QuadraticForm K V) (x : Fin 3 → V) (y : Fin 2 → V) (z : V)
    (hp : Pairwise fun i j ↦ LinearIndependent K ![x i, x j])
    (hy : LinearIndependent K ![y 0, y 1])
    (hx : ∀ i, x i ∈ P) (hyt : ∀ i, y i ∈ T ∧ y i ∉ P)
    (hzP : z ∉ P) (hzT : z ∉ T)
    (hqx : ∀ i, Q (x i) = 0) (hqy : ∀ i, Q (y i) = 0) (hqz : Q z = 0) : Q = 0 := by
  obtain ⟨φ, hφ, hker⟩ := exists_dual_kernel_of_finrank_add_one P (by omega)
  obtain ⟨ψ, hQ⟩ := quadratic_eq_linMulLin_of_zero_on_kernel Q φ hφ
    (by
      intro v hv
      apply quadratic_zero_on_plane_of_three P hP Q x hp hx hqx v
      simpa [hker] using hv)
  have hyψ (i) : ψ (y i) = 0 := by
    have hn : φ (y i) ≠ 0 := by simpa [hker] using (hyt i).2
    exact (mul_eq_zero.mp (by simpa [hQ, QuadraticMap.linMulLin_apply] using hqy i)).resolve_left hn
  have hTψ : T ≤ ψ.ker := by
    rw [← span_pair_eq_of_mem_plane T hT (y 0) (y 1) (hyt 0).1 (hyt 1).1 hy]
    exact Submodule.span_le.mpr (Set.insert_subset_iff.mpr
      ⟨hyψ 0, Set.singleton_subset_iff.mpr (hyψ 1)⟩)
  have hzψ : ψ z = 0 := by
    have hn : φ z ≠ 0 := by simpa [hker] using hzP
    exact (mul_eq_zero.mp (by simpa [hQ, QuadraticMap.linMulLin_apply] using hqz)).resolve_left hn
  have hψ : ψ = 0 := by
    by_contra hψ
    have hd : finrank K ψ.ker = 2 := by
      have hh := ψ.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr (LinearMap.surjective hψ), finrank_top,
        Module.finrank_self, hV] at hh
      omega
    have he := Submodule.eq_of_le_of_finrank_eq hTψ (hT.trans hd.symm)
    exact hzT (he.symm ▸ hzψ)
  ext v
  simp [hQ, hψ, QuadraticMap.linMulLin_apply]

/-- На восьми направлениях трёх лучей удаление одной точки оставляет
достаточно нулей, чтобы квадратичная форма была тождественно нулевой.
Координаты Веронезе не требуются. -/
theorem ThreeRayCover.quadratic_zero_of_erase {I : Type*} [DecidableEq I]
    [FiniteDimensional K V] {μ : I → V} {s : Finset I} {C : Submodule K V}
    (H : ThreeRayCover μ s C)
    (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hV : finrank K V = 3) (hs : 8 ≤ s.card) (j : I)
    (Q : QuadraticForm K V) (hz : ∀ i ∈ s.erase j, Q (μ i) = 0) : Q = 0 := by
  obtain ⟨a, b, c, x, y, z, hab, hac, hbc, hx, hy, hzz⟩ :=
    H.select_indices_three_two_one_after_erase hV hs j
  have houtside (u v : Fin 3) (huv : u ≠ v) (i : I)
      (hi : μ i ∈ H.ray v) (hn : μ i ∉ C) : μ i ∉ H.ray u :=
    fun hu ↦ huv (H.active_ray_unique hV hu hi hn)
  exact quadratic_zero_of_three_two_one hV
    (H.ray a) (H.ray b) (H.finrank_ray a) (H.finrank_ray b) Q
    (fun k ↦ μ (x k)) (fun k ↦ μ (y k)) (μ z)
    (fun k l hkl ↦ hp (x.injective.ne hkl))
    (hp (y.injective.ne (by decide : (0 : Fin 2) ≠ 1)))
    (fun k ↦ (hx k).2)
    (fun k ↦ ⟨(hy k).2.1, houtside a b hab _ (hy k).2.1 (hy k).2.2⟩)
    (houtside a c hac _ hzz.2.1 hzz.2.2)
    (houtside b c hbc _ hzz.2.1 hzz.2.2)
    (fun k ↦ hz _ (hx k).1) (fun k ↦ hz _ (hy k).1) (hz _ hzz.1)

end PlaneVanishing

section SeparatorBudget
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype I]

omit [Fintype I] in
/-- Отделяемые индексы и независимые оставшиеся векторы платятся размерностью.
Лемма общая: квадратичных координат и матриц в её предпосылках нет. -/
theorem separating_forms_card_add_independent_card_le (v : I → V)
    (s t : Finset I) (hst : Disjoint s t)
    (hs : ∀ i ∈ s, ∃ φ : Dual K V, φ (v i) ≠ 0 ∧
      ∀ j, j ≠ i → φ (v j) = 0)
    (ht : LinearIndependent K (fun i : t => v i.val)) :
    s.card + t.card ≤ finrank K V := by
  classical
  let M := Submodule.span K (Set.range fun i : t => v i.val)
  have hm : finrank K M = t.card := by
    simpa [M] using finrank_span_eq_card ht
  have hf (i : s) : ∃ φ : Dual K V, φ (v i.val) ≠ 0 ∧
      ∀ j, j ≠ i.val → φ (v j) = 0 := hs i.val i.property
  choose φ hn hz using hf
  have hmem (i : s) : φ i ∈ M.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    have hker : M ≤ (φ i).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply hz i j.val
      intro he
      exact Finset.disjoint_left.mp hst i.property (he ▸ j.property)
    exact hker
  let ψ (i : s) : M.dualAnnihilator := ⟨φ i, hmem i⟩
  have hφ : LinearIndependent K φ := by
    apply linearIndependent_of_separating_forms φ
      (fun i => Module.Dual.eval K V (v i.val))
    · intro i j hji
      exact hz j i.val (by
        intro he
        exact hji (Subtype.ext he.symm))
    · exact hn
  have hψ : LinearIndependent K ψ :=
    LinearIndependent.of_comp M.dualAnnihilator.subtype hφ
  have hc : s.card ≤ finrank K M.dualAnnihilator := by
    simpa using hψ.fintype_card_le_finrank
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq M
  omega

omit [FiniteDimensional K V] in
/-- Индексы, допускающие отдельную линейную оценку. -/
noncomputable def separatedIndices (v : I → V) : Finset I := by
  classical
  exact Finset.univ.filter fun i => ∃ φ : Dual K V,
    φ (v i) ≠ 0 ∧ ∀ j, j ≠ i → φ (v j) = 0

omit [FiniteDimensional K V] in
@[simp] theorem mem_separatedIndices (v : I → V) (i : I) :
    i ∈ separatedIndices (K := K) v ↔ ∃ φ : Dual K V,
      φ (v i) ≠ 0 ∧ ∀ j, j ≠ i → φ (v j) = 0 := by
  classical
  simp [separatedIndices]

/-- Не менее восьми разных линий в K³ допускают не более трёх сепараторов. -/
theorem quadraticSeparatedIndices_card_le_three (x : I → Fin 3 → K)
    (hx : Pairwise fun i j => LinearIndependent K ![x i, x j])
    (hi : 8 ≤ Fintype.card I) :
    (separatedIndices (K := K) (fun i => quadraticVeronese (x i))).card ≤ 3 := by
  classical
  by_contra hlarge
  have hfour : 4 ≤ (separatedIndices (K := K) (fun i => quadraticVeronese (x i))).card := by
    omega
  obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hfour
  have hthree : 3 ≤ sᶜ.card := by
    rw [Finset.card_compl, hsc]
    omega
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hthree
  have hst : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i his hit
    exact (Finset.mem_compl.mp (ht hit)) his
  let e : t ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using htc)
  have htx : Pairwise fun i j : Fin 3 =>
      LinearIndependent K ![x (e.symm i).val, x (e.symm j).val] := by
    intro i j hij
    apply hx
    intro he
    exact hij (e.symm.injective (Subtype.ext he))
  have hli := (quadraticCoordinates_three_linearIndependent
    (fun i => x (e.symm i).val) htx).comp e e.injective
  have htli : LinearIndependent K (fun i : t => quadraticVeronese (x i.val)) := by
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hli
  have hb := separating_forms_card_add_independent_card_le
    (fun i => quadraticVeronese (x i)) s t hst
    (fun i his => (mem_separatedIndices (K := K) _ i).mp (hs his)) htli
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hsc, htc] at hb
  omega
end SeparatorBudget

section CoordinateTransport
variable {K : Type*} [Field K]

private def quadraticPair : Fin 6 → Fin 3 × Fin 3 :=
  ![(0, 0), (0, 1), (1, 1), (0, 2), (2, 2), (1, 2)]

private theorem quadraticCoordinates_apply_pair (x : Fin 3 → K) (i : Fin 6) :
    quadraticVeronese x i = x (quadraticPair i).1 * x (quadraticPair i).2 := by
  fin_cases i <;> rfl

/-- Любая линейная оценка квадратичных координат есть квадратичная форма.
Обратный мост позволяет использовать общие леммы без смены шести координат. -/
theorem exists_quadratic_form_of_coordinates (ell : Dual K (Fin 6 → K)) :
    ∃ Q : QuadraticForm K (Fin 3 → K), ∀ x, Q x = ell (quadraticVeronese x) := by
  let c := (dotProductEquiv K (Fin 6)).symm ell
  refine ⟨∑ i, c i • QuadraticMap.proj (quadraticPair i).1 (quadraticPair i).2, ?_⟩
  intro x
  have hc : ell (quadraticVeronese x) = c ⬝ᵥ quadraticVeronese x :=
    (DFunLike.congr_fun ((dotProductEquiv K (Fin 6)).apply_symm_apply ell) _).symm
  rw [hc]
  change (∑ i, c i * (x (quadraticPair i).1 * x (quadraticPair i).2)) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [quadraticCoordinates_apply_pair]

end CoordinateTransport

section SpanningCertificate
variable {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

end SpanningCertificate

section ThreePlanePoints
variable {K : Type*} [Field K]

end ThreePlanePoints

section ThreeRayClosure
variable {K I : Type*} [Field K] [DecidableEq I]

/-- У трёхлучевой конфигурации нет ни одного квадратичного сепаратора. -/
theorem ThreeRayCover.not_quadratic_separated [Fintype I]
    {μ : I → Fin 3 → K} {s : Finset I} {C : Submodule K (Fin 3 → K)}
    (H : ThreeRayCover μ s C)
    (hp : Pairwise fun i j => LinearIndependent K ![μ i, μ j])
    (hs : 8 ≤ s.card) (j : I) :
    j ∉ separatedIndices (K := K) (fun i => quadraticVeronese (μ i)) := by
  intro hj
  obtain ⟨ell, hn, hz⟩ := (mem_separatedIndices (K := K) _ j).mp hj
  obtain ⟨Q, hQ⟩ := exists_quadratic_form_of_coordinates ell
  have hzero : Q = 0 := H.quadratic_zero_of_erase hp (by simp) hs j Q (by
    intro i hi
    rw [hQ]
    exact hz i (Finset.mem_erase.mp hi).1)
  exact hn ((hQ (μ j)).symm.trans (by simp [hzero]))

end ThreeRayClosure

end MMRank
