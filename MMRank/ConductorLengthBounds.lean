module

public import MMRank.PhysicalConductorBounds
public import MMRank.RestrictedConductorBounds
public import MMRank.NormalizedHyperplane
public import MMRank.InfiniteExtension

@[expose] public section

/-! # Первые безусловные оценки длины из двух сторон кондукторного метода

Нормировка и бесконечное расширение применяются к данному алгоритму.
Равенство минимальных рангов при расширении поля не предполагается.
-/

namespace MMRank.ExactAlgorithm

open Module

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Размерностный сертификат над бесконечным полем после нормировки.
Числа d,e являются размерностями построенной насыщенной пары. -/
theorem exists_conductor_dimension_bounds_of_infinite [Infinite K]
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S ι) (hn : alg.toCoefficients.NonzeroTerms)
    (hp : Fintype.card P = 3) (hq : 2 ≤ Fintype.card Q)
    (ht : 2 ≤ Fintype.card S * (Fintype.card Q - 1)) :
    ∃ d e : ℕ, d ≤ e ∧
      3 * (Fintype.card P * Fintype.card S) + 2 ≤
        d + 2 * (Fintype.card ι - Fintype.card S * (Fintype.card Q - 1)) ∧
      Fintype.card P * Fintype.card S + (Fintype.card Q - 1) * e ≤ Fintype.card ι := by
  obtain ⟨u, ⟨h⟩⟩ := alg.exists_normalized_hyperplane_core hn hq
  let a := alg.rescale u
  let M := a.toCoefficients.alphaOn h.F
  let N := a.toCoefficients.gamma.range
  refine ⟨finrank K (conductor N M), finrank K (M * conductor N M),
    Submodule.finrank_mono (le_mul_of_one_mem M _ h.one_mem), ?_, ?_⟩
  · have hF := h.codim_one
    exact a.restricted_conductor_strengthened_bound h.F 1 (by omega) (by omega)
      h.one_mem (by omega) ht h.beta_support h.restricted_nz
  · exact a.saturated_physical_length_bound_of_hyperplane h.F h.codim_one

/-- Сертификат существует над произвольным исходным полем.
Построение d,e допускает переход в K(t); вывод — неравенства для исходной длины. -/
theorem exists_conductor_dimension_bounds (alg : ExactAlgorithm K P Q S ι)
    (hp : Fintype.card P = 3) (hq : 2 ≤ Fintype.card Q)
    (ht : 2 ≤ Fintype.card S * (Fintype.card Q - 1)) :
    ∃ d e : ℕ, d ≤ e ∧
      3 * (Fintype.card P * Fintype.card S) + 2 ≤
        d + 2 * (Fintype.card ι - Fintype.card S * (Fintype.card Q - 1)) ∧
      Fintype.card P * Fintype.card S + (Fintype.card Q - 1) * e ≤ Fintype.card ι := by
  have hs : 0 < Fintype.card S := by
    by_contra! hh
    have hz : Fintype.card S = 0 := by omega
    simp [hz] at ht
  let : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty S := Fintype.card_pos_iff.mp hs
  let : Infinite (RatFunc K) := ratFunc_infinite K
  obtain ⟨a, ha⟩ := alg.exists_nonzero_length_ratFunc (by rw [hp]; omega)
    (Fintype.card ι) le_rfl
  simpa only [Fintype.card_fin] using a.exists_conductor_dimension_bounds_of_infinite ha hp hq ht

/-- Общая прямоугольная оценка для формата ⟨3,2,s⟩ при s≥2. -/
theorem length_bound_three_by_two (alg : ExactAlgorithm K P Q S ι)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 2) (hs : 2 ≤ Fintype.card S) :
    14 * Fintype.card S + 2 ≤ 3 * Fintype.card ι := by
  obtain ⟨d, e, hde, hlo, hhi⟩ := alg.exists_conductor_dimension_bounds hp
    (by omega) (by simpa [hq] using hs)
  simp only [hp, hq] at hlo hhi
  omega

end MMRank.ExactAlgorithm
