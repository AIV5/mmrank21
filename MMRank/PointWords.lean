import MMRank.ConnectivityCost

/-! # Точечные слова и одномерные ограничения множителей

Общая собственная прямая поточечного действия эквивалентна носителю внутри
одного блока, на котором каждый множитель постоянен. Размер поддержки не фиксирован.
-/

namespace MMRank

open Module

variable {K ι : Type*} [Field K]

/-- Ненулевое общее собственное слово для всех поточечных множителей M. -/
def IsPointWord (M : Submodule K (ι → K)) (w : ι → K) : Prop :=
  w ≠ 0 ∧ ∀ m ∈ M, ∃ a : K, m * w = a • w

/-- В N нет ненулевых слов, лежащих на одной общей собственной прямой M. -/
def HasNoPointWords (M N : Submodule K (ι → K)) : Prop :=
  ∀ w ∈ N, ¬ IsPointWord M w

theorem HasNoPointWords.mono {M N T : Submodule K (ι → K)}
    (h : HasNoPointWords M T) (hle : N ≤ T) : HasNoPointWords M N :=
  fun w hw ↦ h w (hle hw)

/-- Точечное слово любого пространства уже лежит в его кондукторе. -/
theorem IsPointWord.mem_conductor {M N : Submodule K (ι → K)} {w : ι → K}
    (hp : IsPointWord M w) (hw : w ∈ N) : w ∈ conductor N M := by
  apply MMRank.mem_conductor.mpr
  intro m hm
  obtain ⟨a, ha⟩ := hp.2 m hm
  rw [ha]
  exact N.smul_mem a hw

/-- Собственная прямая эквивалентна постоянству каждого множителя на носителе.
Носитель слова не обязан совпадать со всем общим собственным блоком. -/
theorem isPointWord_iff_constant_on_support (M : Submodule K (ι → K)) (w : ι → K) :
    IsPointWord M w ↔ w ≠ 0 ∧
      ∀ m ∈ M, ∀ i j, w i ≠ 0 → w j ≠ 0 → m i = m j := by
  constructor
  · rintro ⟨hw, he⟩
    refine ⟨hw, ?_⟩
    intro m hm i j hi hj
    obtain ⟨a, ha⟩ := he m hm
    have hmi : m i = a := (mul_right_cancel₀ hi) (congrFun ha i)
    have hmj : m j = a := (mul_right_cancel₀ hj) (congrFun ha j)
    exact hmi.trans hmj.symm
  · rintro ⟨hw, hc⟩
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra! h
      exact hw (funext h)
    refine ⟨hw, ?_⟩
    intro m hm
    refine ⟨m i, ?_⟩
    ext j
    by_cases hj : w j = 0
    · simp [hj]
    · change m j * w j = m i * w j
      rw [hc m hm j i hj hi]

/-- Если M содержит единицу, одномерное ограничение состоит из констант. -/
theorem restriction_constant_of_finrank_le_one (M : Submodule K (ι → K))
    [FiniteDimensional K M] (h1 : (1 : ι → K) ∈ M) (s : Set ι) (hs : s.Nonempty)
    (hd : finrank K (coordinateRestriction M s).range ≤ 1) :
    ∀ m ∈ M, ∃ a : K, ∀ i ∈ s, m i = a := by
  have hone : (1 : s → K) ∈ (coordinateRestriction M s).range := ⟨⟨1, h1⟩, rfl⟩
  have hn : (1 : s → K) ≠ 0 := by
    obtain ⟨i, hi⟩ := hs
    intro hh
    exact one_ne_zero (congrFun hh ⟨i, hi⟩)
  have hlo := Submodule.finrank_mono
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hone)
  rw [finrank_span_singleton hn] at hlo
  have he := eq_span_singleton_of_mem_of_finrank_eq_one (Nat.le_antisymm hd hlo) hone hn
  intro m hm
  have hr : coordinateRestriction M s ⟨m, hm⟩ ∈ (coordinateRestriction M s).range :=
    ⟨⟨m, hm⟩, rfl⟩
  rw [he, Submodule.mem_span_singleton] at hr
  obtain ⟨a, ha⟩ := hr
  refine ⟨a, ?_⟩
  intro i hi
  simpa using (congrFun ha ⟨i, hi⟩).symm

/-- Ненулевое слово, поддержанное на блоке с одномерным ограничением, точечно. -/
theorem isPointWord_of_supported_of_restriction_finrank_le_one
    (M : Submodule K (ι → K)) [FiniteDimensional K M]
    (h1 : (1 : ι → K) ∈ M) (s : Set ι) (w : ι → K) (hw : w ≠ 0)
    (hsupp : ∀ i ∉ s, w i = 0)
    (hd : finrank K (coordinateRestriction M s).range ≤ 1) : IsPointWord M w := by
  have hs : s.Nonempty := by
    by_contra h
    apply hw
    ext i
    exact hsupp i (fun hi ↦ h ⟨i, hi⟩)
  refine ⟨hw, ?_⟩
  intro m hm
  obtain ⟨a, ha⟩ := restriction_constant_of_finrank_le_one M h1 s hs hd m hm
  refine ⟨a, ?_⟩
  ext i
  by_cases hi : i ∈ s
  · change m i * w i = a * w i
    rw [ha i hi]
  · simp [hsupp i hi]

/-- Любая активная устойчивая компонента пространства без точечных слов
имеет ограничение M размерности хотя бы два. -/
theorem two_le_restriction_finrank_of_noPointWords
    (M N : Submodule K (ι → K)) [FiniteDimensional K M]
    (h1 : (1 : ι → K) ∈ M) (hn : HasNoPointWords M N) (s : Set ι)
    (hst : ∀ w ∈ N, coordinateProjection K s w ∈ N)
    (hactive : ∃ w ∈ N, ∃ i ∈ s, w i ≠ 0) :
    2 ≤ finrank K (coordinateRestriction M s).range := by
  classical
  by_contra h
  have hd : finrank K (coordinateRestriction M s).range ≤ 1 := by omega
  obtain ⟨w, hw, i, hi, hwi⟩ := hactive
  have hp : coordinateProjection K s w ≠ 0 := by
    intro hz
    have := congrFun hz i
    simp [hi] at this
    exact hwi this
  exact hn _ (hst w hw) (isPointWord_of_supported_of_restriction_finrank_le_one M h1 s
    (coordinateProjection K s w) hp (by intro j hj; simp [hj]) hd)

/-- Отсутствие делителей нуля с пространством множителей размерности ≥2
исключает точечные слова. Единица и полный носитель не требуются. -/
theorem hasNoPointWords_of_noZeroDivisors (M N : Submodule K (ι → K))
    [FiniteDimensional K M] (hM : 2 ≤ finrank K M)
    (hnz : ∀ a ∈ M, ∀ w ∈ N, a * w = 0 → a = 0 ∨ w = 0) :
    HasNoPointWords M N := by
  intro w hw hp
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! h
    exact hp.1 (funext h)
  have hker : (coordinateEval M i).ker ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [Module.finrank_self]; omega)
  obtain ⟨a, ha, ha0⟩ := (coordinateEval M i).ker.ne_bot_iff.mp hker
  have hai : a.val i = 0 := ha
  obtain ⟨c, hc⟩ := hp.2 a.val a.property
  have hci : c = 0 := by
    have hh : a.val i * w i = c * w i := congrFun hc i
    rw [hai, zero_mul, eq_comm, mul_eq_zero] at hh
    exact hh.resolve_right hi
  have hmul : a.val * w = 0 := by simpa only [hci, zero_smul] using hc
  rcases hnz a.val a.property w hw hmul with hz | hz
  · exact ha0 (Subtype.ext hz)
  · exact hp.1 hz

/-- Любая ненулевая координата точечного слова задаёт его собственное значение. -/
theorem IsPointWord.mul_eq_coordinate {M : Submodule K (ι → K)} {w : ι → K}
    (hp : IsPointWord M w) {i : ι} (hi : w i ≠ 0) {a : ι → K} (ha : a ∈ M) :
    a * w = a i • w := by
  obtain ⟨c, hc⟩ := hp.2 a ha
  have he : a i = c := mul_right_cancel₀ hi (congrFun hc i)
  simpa only [he] using hc

end MMRank
