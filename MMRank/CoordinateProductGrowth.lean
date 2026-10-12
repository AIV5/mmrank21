import MMRank.CoordinateDuality

/-! # Рост произведения координатных пространств без делителей нуля

Индукция по размерности множителей с занулением одной активной координаты.
Поле произвольно; единица и насыщенность не нужны.
-/

namespace MMRank

open Module

variable {K ι : Type*} [Field K] [Finite ι]

/-- Любой ненулевой множитель инъективно вкладывает второй фактор в произведение. -/
theorem finrank_right_le_product_of_noZeroDivisors (M N : Submodule K (ι → K))
    (hM : M ≠ ⊥)
    (hnz : ∀ a ∈ M, ∀ b ∈ N, a * b = 0 → a = 0 ∨ b = 0) :
    finrank K N ≤ finrank K (M * N) := by
  obtain ⟨a, ha, ha0⟩ := M.ne_bot_iff.mp hM
  let f : N →ₗ[K] M * N :=
    ((LinearMap.mulLeft K a).domRestrict N).codRestrict (M * N)
      (fun b ↦ Submodule.mul_mem_mul ha b.property)
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro b hb
    apply Subtype.ext
    exact (hnz a ha b.val b.property (congrArg Subtype.val hb)).resolve_left ha0
  exact LinearMap.finrank_le_finrank_of_injective hi

/-- Общая оценка dim M+dim N≤dim(MN)+1 для ненулевых координатных пространств
без делителей нуля. В отличие от общей билинейной леммы, замкнутость поля не нужна. -/
theorem coordinate_product_growth_of_noZeroDivisors (M N : Submodule K (ι → K))
    (hM : M ≠ ⊥) (hN : N ≠ ⊥)
    (hnz : ∀ a ∈ M, ∀ b ∈ N, a * b = 0 → a = 0 ∨ b = 0) :
    finrank K M + finrank K N ≤ finrank K (M * N) + 1 := by
  generalize hm : finrank K M = m
  induction m using Nat.strong_induction_on generalizing M with
  | h m ih =>
    by_cases hm1 : m ≤ 1
    · have hh := finrank_right_le_product_of_noZeroDivisors M N hM hnz
      omega
    obtain ⟨a, ha, ha0⟩ := M.ne_bot_iff.mp hM
    obtain ⟨b, hb, hb0⟩ := N.ne_bot_iff.mp hN
    have hab : a * b ≠ 0 := fun hz ↦ (hnz a ha b hb hz).elim ha0 hb0
    obtain ⟨i, hi⟩ : ∃ i, (a * b) i ≠ 0 := by
      by_contra! hh
      exact hab (funext hh)
    let E := M * N
    have he : coordinateEval E i ≠ 0 := (coordinateEval_ne_zero_iff E i).mpr
      ⟨a * b, Submodule.mul_mem_mul ha hb, hi⟩
    have hem : coordinateEval M i ≠ 0 := (coordinateEval_ne_zero_iff M i).mpr
      ⟨a, ha, fun hz ↦ hi (by simp [hz])⟩
    let M₀ := (coordinateEval M i).ker.map M.subtype
    let E₀ := (coordinateEval E i).ker.map E.subtype
    have hdM : finrank K M₀ + 1 = finrank K M := by
      rw [Submodule.finrank_map_subtype_eq]
      exact Module.Dual.finrank_ker_add_one_of_ne_zero hem
    have hdE : finrank K E₀ + 1 = finrank K E := by
      rw [Submodule.finrank_map_subtype_eq]
      exact Module.Dual.finrank_ker_add_one_of_ne_zero he
    have hM₀ : M₀ ≤ M := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    have hn₀ : M₀ ≠ ⊥ := by
      intro hz
      rw [hz, finrank_bot] at hdM
      omega
    have hprod : M₀ * N ≤ E₀ := by
      apply Submodule.mul_le.mpr
      intro x hx y hy
      obtain ⟨x, hx, rfl⟩ := hx
      refine ⟨⟨x.val * y, Submodule.mul_mem_mul x.property hy⟩, ?_, rfl⟩
      change x.val i * y i = 0
      have hxi : x.val i = 0 := hx
      rw [hxi, zero_mul]
    have hrec := ih (finrank K M₀) (by omega) M₀ hn₀
      (fun x hx y hy ↦ hnz x (hM₀ hx) y hy) rfl
    have hle := Submodule.finrank_mono hprod
    change finrank K E₀ + 1 = finrank K (M * N) at hdE
    omega

end MMRank
