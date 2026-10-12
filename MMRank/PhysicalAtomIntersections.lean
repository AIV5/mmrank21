import MMRank.PhysicalAtom

/-! # Пересечение соседних физических атомов в произвольных размерах -/
namespace MMRank.ExactAlgorithm.PhysicalAtom
open Matrix
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  {alg : ExactAlgorithm K P Q S I}

/-- Нулевое значение физической пары делает носители непересекающимися. -/
theorem disjoint_of_pairing_eq_zero (a : PhysicalAtom alg) (b : PhysicalAtom alg.rotate)
    (hp : b.last ⬝ᵥ a.first = 0) : Disjoint a.support b.support := by
  apply Set.disjoint_left.mpr
  intro i hi hj
  have hw := b.V_mem hj
  obtain ⟨rows, he⟩ := hw
  have hzero : alg.W i *ᵥ a.first = 0 := by
    ext r
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (rows r).property
    have hrow : alg.W i r = k • b.last := by
      have hh := congrFun he r
      exact hh.symm.trans hk.symm
    change alg.W i r ⬝ᵥ a.first = 0
    rw [hrow, smul_dotProduct, hp, smul_zero]
  apply hi
  change trace (alg.W i * vecMulVec a.first a.last) = 0
  rw [mul_vecMulVec, hzero]
  rw [zero_vecMulVec, trace_zero]

/-- Ненулевое произведение двух физических тестов обязано иметь слагаемое
из пересечения носителей. Обратное следует из фиксированного выхода атома. -/
theorem inter_nonempty_iff (a : PhysicalAtom alg) (b : PhysicalAtom alg.rotate) :
    (a.support ∩ b.support).Nonempty ↔ b.last ⬝ᵥ a.first ≠ 0 := by
  constructor
  · rintro ⟨i, ha, hb⟩ hp
    exact Set.disjoint_left.mp (a.disjoint_of_pairing_eq_zero b hp) ha hb
  · intro hp
    by_contra hn
    have hz : b.test * a.test = 0 := by
      have hh := alg.rotate.rotate.exact_formula a.test b.test
      change b.test * a.test = ∑ i, (alg.toCoefficients.gamma a.test i *
        alg.rotate.toCoefficients.gamma b.test i) • alg.V i at hh
      rw [hh]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : alg.toCoefficients.gamma a.test i = 0
      · simp only [hi, zero_mul, zero_smul]
      · have hj : alg.rotate.toCoefficients.gamma b.test i = 0 := by
          by_contra hj
          exact hn ⟨i, hi, hj⟩
        simp only [hj, mul_zero, zero_smul]
    obtain ⟨q, hq⟩ : ∃ q, b.first q ≠ 0 := by simpa [funext_iff] using b.first_ne_zero
    obtain ⟨s, hs⟩ : ∃ s, a.last s ≠ 0 := by simpa [funext_iff] using a.last_ne_zero
    have hh := congrFun (congrFun hz q) s
    change (vecMulVec b.first b.last * vecMulVec a.first a.last) q s = 0 at hh
    rw [vecMulVec_mul_vecMulVec] at hh
    exact mul_ne_zero hq (mul_ne_zero hp hs) hh

/-- Критерий непересечения эквивалентен единственному скалярному равенству. -/
theorem disjoint_iff (a : PhysicalAtom alg) (b : PhysicalAtom alg.rotate) :
    Disjoint a.support b.support ↔ b.last ⬝ᵥ a.first = 0 := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    a.inter_nonempty_iff b, not_ne_iff]

end MMRank.ExactAlgorithm.PhysicalAtom
