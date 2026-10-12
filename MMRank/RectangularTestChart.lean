module

public import MMRank.RegularSliceChart
public import MMRank.SupportedTestSpace

@[expose] public section

namespace MMRank
open Matrix Module
variable {K P S : Type*} [Field K] [Fintype P] [Fintype S]

/-- Подпространство матричных тестов с ограниченными колонками и строками
имеет точную меньшую матричную модель. Оба входа поднимаются независимо. -/
theorem exists_rectangular_test_chart_rank
    (T : Submodule K (Matrix P S K)) (F : Submodule K (P → K))
    (H : Submodule K (S → K)) (p s : ℕ) (hF : finrank K F = p) (hH : finrank K H = s)
    (hcols : ∀ C ∈ T, C.transpose ∈ matricesInto F)
    (hrows : ∀ C ∈ T, C ∈ matricesInto H) :
    ∃ (E : Matrix (Fin p) (Fin s) K →ₗ[K] Matrix P S K)
      (L : Matrix (Fin p) P K) (R : Matrix S (Fin s) K),
      Function.Injective E ∧ T ≤ E.range ∧
      (∀ C, L * E C * R = C) ∧
      (∀ C A : Matrix (Fin p) (Fin s) K,
        trace (E C * (R * A.transpose * L)) = trace (C * A.transpose)) ∧
      (∀ C, (E C).rank = C.rank) := by
  obtain ⟨_, L, R, E, _, _, hi, ht, hr, he, _⟩ :=
    exists_two_sided_slice_chart (Q := Unit) T F H p s hF hH hcols hrows
  refine ⟨E, L, R, hi, ht, he, ?_, hr⟩
  intro C A
  calc
    trace (E C * (R * A.transpose * L)) =
        trace ((L * E C * R) * A.transpose) := by
      rw [← Matrix.mul_assoc, trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = trace (C * A.transpose) := by rw [he]

/-- Размерность подпространства сохраняется при точной меньшей модели. -/
theorem finrank_comap_of_injective_of_le_range
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (E : V →ₗ[K] W) (hE : Function.Injective E) (T : Submodule K W) (hT : T ≤ E.range) :
    finrank K (T.comap E) = finrank K T := by
  have he := (Submodule.equivMapOfInjective E hE (T.comap E)).finrank_eq
  rw [Submodule.map_comap_eq, inf_eq_right.mpr hT] at he
  exact he

end MMRank
