import MMRank.CoordinateJointSymmetrizers

/-! # Линейный фактор семейства пропорциональных прямоугольных блоков -/
namespace MMRank
open Matrix
variable {K P S Q Z : Type*} [Field K] [Fintype P] [Fintype S]
  [DecidableEq P] [DecidableEq S] [AddCommGroup Z] [Module K Z]

/-- Пропорциональные блоки дают линейный второй фактор, а не произвольный
выбор коэффициента отдельно при каждом z. -/
theorem exists_linear_factor_of_proportional_matrix_blocks
    (B : Z →ₗ[K] (P → K) →ₗ[K] (S → K) →ₗ[K] (Q → K))
    (T : Matrix S P K) (hT : T ≠ 0)
    (hU : ∀ zq, ∃ a : K, jointSymmetrizerBlocks B zq = a • T) :
    ∃ f : Z →ₗ[K] (Q → K), ∀ z u s,
      B z u s = (s ⬝ᵥ (T *ᵥ u)) • f z := by
  obtain ⟨s₀, p₀, hc⟩ : ∃ s p, T s p ≠ 0 := by
    by_contra! hh
    have hz : T = 0 := by ext s p; exact hh s p
    exact hT hz
  let c := T s₀ p₀
  let f : Z →ₗ[K] (Q → K) :=
    { toFun := fun z ↦ c⁻¹ • B z (Pi.single p₀ 1) (Pi.single s₀ 1)
      map_add' := by intro z w; simp [map_add, smul_add]
      map_smul' := by intro a z; simp [smul_smul, mul_comm] }
  have hb (z : Z) (q : Q) : jointSymmetrizerBlocks B (z, q) =
      f z q • T := by
    obtain ⟨a, ha⟩ := hU (z, q)
    have hh := congrFun (congrFun ha s₀) p₀
    have hf : f z q = a := by
      change c⁻¹ * B z (Pi.single p₀ 1) (Pi.single s₀ 1) q = a
      change B z (Pi.single p₀ 1) (Pi.single s₀ 1) q = a * c at hh
      rw [hh]
      simp [c, hc, mul_left_comm]
    rw [hf]; exact ha
  refine ⟨f, ?_⟩
  intro z u s
  have he (i : S) (q : Q) : B z u (Pi.single i 1) q =
      f z q * (T *ᵥ u) i := by
    rw [← jointSymmetrizerBlocks_mulVec_apply, hb, smul_mulVec]
    rfl
  ext q
  rw [LinearMap.pi_apply_eq_sum_univ (B z u)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun j : S ↦ if i = j then (1 : K) else 0) = Pi.single i 1 := by
    ext j; simp [Pi.single_apply, eq_comm]
  rw [hi, he]
  ring

/-- Отсутствие делителей нуля обеспечивает инъективность второго
фактора. Первый блок может быть прямоугольным. -/
theorem exists_injective_linear_factor_of_proportional_matrix_blocks [Nonempty P]
    (B : Z →ₗ[K] (P → K) →ₗ[K] (S → K) →ₗ[K] (Q → K))
    (T : Matrix S P K) (hT : T ≠ 0)
    (hU : ∀ zq, ∃ a : K, jointSymmetrizerBlocks B zq = a • T)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0) :
    ∃ f : Z →ₗ[K] (Q → K), Function.Injective f ∧ ∀ z u s,
      B z u s = (s ⬝ᵥ (T *ᵥ u)) • f z := by
  obtain ⟨f, he⟩ := exists_linear_factor_of_proportional_matrix_blocks B T hT hU
  refine ⟨f, ?_, he⟩
  intro z w hzw
  apply sub_eq_zero.mp
  let i : P := Classical.arbitrary P
  have hz : B (z - w) (Pi.single i 1) = 0 := by
    apply LinearMap.ext
    intro s
    rw [he, map_sub, hzw, sub_self, smul_zero]
    rfl
  rcases hnz (z - w) (Pi.single i 1) hz with h | h
  · exact h
  · have hh := congrFun h i
    simp at hh

end MMRank
