module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import MMRank.RankOneMinors
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! # Внешнее произведение над областью с gcd

Используется
делимость общего делителя конечного семейства. Однородность и степени
полиномиальных множителей здесь ещё не утверждаются.
-/

namespace MMRank

open Matrix

/-- Примитивный вектор: общая делимость всех a u_i влечёт делимость a. -/
theorem dvd_of_dvd_mul_primitive
    {R I : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R] [Fintype I]
    (u : I → R) (hu : Finset.univ.gcd u = 1) (a b : R)
    (h : ∀ i, b ∣ u i * a) : b ∣ a := by
  have hh : b ∣ Finset.univ.gcd (fun i ↦ u i * a) := Finset.dvd_gcd (by simpa using h)
  have ha := Finset.gcd_mul_right' Finset.univ u a
  rw [ha.dvd_iff_dvd_right, hu, one_mul] at hh
  exact hh

/-- Ненулевая матрица с нулевыми минорами порядка два над GCD-областью
есть внешнее произведение. Число столбцов произвольно, конечны только строки. -/
theorem exists_primitive_outerProduct_of_minors_eq_zero
    {R I J : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R] [Fintype I]
    (N : Matrix I J R) (hN : N ≠ 0)
    (hm : ∀ i k j l, N i j * N k l = N i l * N k j) :
    ∃ u : I → R, ∃ v : J → R,
      (∀ i j, N i j = u i * v j) ∧ Finset.univ.gcd u = 1 := by
  classical
  obtain ⟨i₀, j₀, hn⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra! h
    apply hN
    ext i j
    exact h i j
  obtain ⟨u, hu, hprim⟩ := Finset.extract_gcd (fun i ↦ N i j₀)
    (show (Finset.univ : Finset I).Nonempty from ⟨i₀, Finset.mem_univ _⟩)
  have hcol (i) : N i j₀ = Finset.univ.gcd (fun i ↦ N i j₀) * u i := hu i (Finset.mem_univ _)
  have hg : Finset.univ.gcd (fun i ↦ N i j₀) ≠ 0 := by
    intro hz
    exact hn (by rw [hcol, hz, zero_mul])
  have hui : u i₀ ≠ 0 := by
    intro hz
    exact hn (by rw [hcol, hz, mul_zero])
  have hrel (i k j) : u i * N k j = u k * N i j := by
    apply mul_left_cancel₀ hg
    calc
      _ = N i j₀ * N k j := by rw [← mul_assoc, ← hcol]
      _ = N i j * N k j₀ := hm i k j₀ j
      _ = _ := by rw [hcol]; ring
  have hd (j) : u i₀ ∣ N i₀ j := by
    apply dvd_of_dvd_mul_primitive u hprim
    intro k
    rw [← hrel i₀ k j]
    exact dvd_mul_right _ _
  choose v hv using hd
  refine ⟨u, v, ?_, hprim⟩
  intro i j
  apply mul_left_cancel₀ hui
  calc
    _ = u i * N i₀ j := hrel i₀ i j
    _ = _ := by rw [hv]; ring

/-- Критерий внешнего произведения над любой GCD-областью, включая нулевую
матрицу и пустые наборы индексов. Выбор нормированного gcd скрыт в доказательстве. -/
theorem exists_outerProduct_iff_minors_eq_zero
    {R I J : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R] [Fintype I]
    (N : Matrix I J R) :
    (∃ u : I → R, ∃ v : J → R, ∀ i j, N i j = u i * v j) ↔
      ∀ i k j l, N i j * N k l = N i l * N k j := by
  constructor
  · rintro ⟨u, v, h⟩ i k j l
    simp only [h]
    ring
  · intro h
    by_cases hn : N = 0
    · exact ⟨0, 0, by simp [hn]⟩
    let : NormalizedGCDMonoid R := Classical.choice inferInstance
    obtain ⟨u, v, huv, _⟩ := exists_primitive_outerProduct_of_minors_eq_zero N hn h
    exact ⟨u, v, huv⟩

end MMRank
