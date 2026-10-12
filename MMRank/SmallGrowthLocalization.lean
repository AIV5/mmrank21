module

public import MMRank.PointWords
public import MMRank.ConductorBoundaryTransfer

@[expose] public section

/-! # Локализация малого роста и нижняя кондукторная граница

Без точечных слов каждый активный блок растёт. При ненулевом кондукторе
и приросте ≤1 активный блок единственен и множители на нём двумерны.
Полный носитель требуется лишь для короткого следствия о границе ≥2.
-/

namespace MMRank

open Module

set_option backward.isDefEq.respectTransparency false

variable {K ι : Type*} [Field K] [Finite ι]

/-- При отсутствии точечных слов каждый активный блок насыщенной пары
имеет нетривиальное ограничение множителей. -/
theorem saturated_component_two_le_restriction_finrank
    (M N : Submodule K (ι → K)) (h1 : (1 : ι → K) ∈ M)
    (hn : HasNoPointWords M (M * conductor N M)) (i : ι)
    (hi : ∃ w ∈ M * conductor N M, w i ≠ 0) :
    2 ≤ finrank K (coordinateRestriction M (coordinateComponent (M * conductor N M) i)).range := by
  apply two_le_restriction_finrank_of_noPointWords M _ h1 hn _
    (coordinateComponent_stable _ i)
  obtain ⟨w, hw, hwi⟩ := hi
  exact ⟨w, hw, i, mem_coordinateComponent_self _ i, hwi⟩

/-- Если прирост не больше единицы, любые два активных индекса
пространства без точечных слов лежат в одной канонической компоненте. -/
theorem saturated_components_eq_of_growth_le_one
    (M N : Submodule K (ι → K)) (h1 : (1 : ι → K) ∈ M)
    (hn : HasNoPointWords M (M * conductor N M))
    (hg : finrank K (M * conductor N M) - finrank K (conductor N M) ≤ 1)
    (i j : ι) (hi : ∃ w ∈ M * conductor N M, w i ≠ 0)
    (hj : ∃ w ∈ M * conductor N M, w j ≠ 0) :
    coordinateComponent (M * conductor N M) i = coordinateComponent (M * conductor N M) j := by
  classical
  let E := M * conductor N M
  let β := Set.range (coordinateComponent E)
  let : Fintype β := Fintype.ofFinite β
  let ci : β := ⟨coordinateComponent E i, ⟨i, rfl⟩⟩
  let cj : β := ⟨coordinateComponent E j, ⟨j, rfl⟩⟩
  have hc := (saturated_nontrivial_components_card_le M N h1).trans hg
  have hic : ci ∈ Finset.univ.filter (fun c : β ↦
      2 ≤ finrank K (coordinateRestriction M c.val).range) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      saturated_component_two_le_restriction_finrank M N h1 hn i hi⟩
  have hjc : cj ∈ Finset.univ.filter (fun c : β ↦
      2 ≤ finrank K (coordinateRestriction M c.val).range) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      saturated_component_two_le_restriction_finrank M N h1 hn j hj⟩
  exact congrArg Subtype.val (Finset.card_le_one.mp hc ci hic cj hjc)

/-- Локализация малого роста: единственная активная компонента есть общий носитель,
прирост равен одному, а ограничение множителей на носитель двумерно.
Полный носитель не предполагается. -/
theorem saturated_small_growth_localization
    (M N : Submodule K (ι → K)) (h1 : (1 : ι → K) ∈ M)
    (hD : conductor N M ≠ ⊥) (hn : HasNoPointWords M (M * conductor N M))
    (hg : finrank K (M * conductor N M) - finrank K (conductor N M) ≤ 1) :
    finrank K (M * conductor N M) - finrank K (conductor N M) = 1 ∧
      ∃ i : ι, (∃ w ∈ M * conductor N M, w i ≠ 0) ∧
        coordinateComponent (M * conductor N M) i = {j | ∃ d ∈ conductor N M, d j ≠ 0} ∧
        finrank K (coordinateRestriction M {j | ∃ d ∈ conductor N M, d j ≠ 0}).range = 2 := by
  obtain ⟨d, hd, hd0⟩ := (conductor N M).ne_bot_iff.mp hD
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra! h
    exact hd0 (funext h)
  have hei : ∃ w ∈ M * conductor N M, w i ≠ 0 :=
    ⟨d, le_mul_of_one_mem M _ h1 hd, hi⟩
  have hlo := saturated_component_two_le_restriction_finrank M N h1 hn i hei
  have hup := saturated_component_restriction_finrank_le M N h1 i
  have heq : finrank K (M * conductor N M) - finrank K (conductor N M) = 1 := by omega
  have hdim : finrank K (coordinateRestriction M (coordinateComponent (M * conductor N M) i)).range = 2 := by
    omega
  have hs : coordinateComponent (M * conductor N M) i = {j | ∃ d ∈ conductor N M, d j ≠ 0} := by
    ext j
    constructor
    · intro hj
      exact (product_coord_nonzero_iff M (conductor N M) h1 j).mp
        (coordinateComponent_subset_support _ i hei hj)
    · intro hj
      have hej := (product_coord_nonzero_iff M (conductor N M) h1 j).mpr hj
      rw [saturated_components_eq_of_growth_le_one M N h1 hn hg i j hei hej]
      exact mem_coordinateComponent_self _ j
  exact ⟨heq, i, hei, hs, hs ▸ hdim⟩

omit [Finite ι] in
/-- Ограничение на все координаты не меняет размерности. -/
theorem finrank_coordinateRestriction_univ (M : Submodule K (ι → K)) :
    finrank K (coordinateRestriction M Set.univ).range = finrank K M := by
  apply LinearMap.finrank_range_of_inj
  intro x y h
  apply Subtype.ext
  ext i
  exact congrFun h ⟨i, Set.mem_univ i⟩

/-- Достаточно трёх измерений множителей на носителе T:
полный носитель T для потери двух измерений не требуется. -/
theorem two_le_conductor_boundary_of_restriction_finrank
    (M T : Submodule K (ι → K)) (h1 : (1 : ι → K) ∈ M)
    (hM : 3 ≤ finrank K (coordinateRestriction M {i | ∃ w ∈ T, w i ≠ 0}).range)
    (hT : 2 ≤ finrank K T) (hn : HasNoPointWords M T) :
    2 ≤ finrank K T - finrank K (conductor T M) := by
  by_contra h
  have hsmall : finrank K T - finrank K (conductor T M) ≤ 1 := by omega
  have hDT := Submodule.finrank_mono (conductor_le_of_one_mem T M h1)
  have hET := Submodule.finrank_mono (mul_conductor_le M T)
  have hDE := Submodule.finrank_mono (le_mul_of_one_mem M (conductor T M) h1)
  have hD : conductor T M ≠ ⊥ := by
    intro hz
    have hz' : finrank K (conductor T M) = 0 := by simp [hz]
    omega
  have hg : finrank K (M * conductor T M) - finrank K (conductor T M) ≤ 1 := by omega
  obtain ⟨he, i, _, _, hdim⟩ := saturated_small_growth_localization M T h1 hD
    (hn.mono (mul_conductor_le M T)) hg
  have hEq : M * conductor T M = T := by
    apply Submodule.eq_of_le_of_finrank_eq (mul_conductor_le M T)
    omega
  have hsupp : {j | ∃ d ∈ conductor T M, d j ≠ 0} = {j | ∃ w ∈ T, w j ≠ 0} := by
    ext j
    have hh := product_coord_nonzero_iff M (conductor T M) h1 j
    rw [hEq] at hh
    exact hh.symm
  rw [hsupp] at hdim
  omega

/-- Полный носитель и отсутствие точечных слов заставляют кондуктор
терять не меньше двух измерений. Частный случай теоремы об ограничении на носитель. -/
theorem two_le_conductor_boundary_of_noPointWords
    (M T : Submodule K (ι → K)) (h1 : (1 : ι → K) ∈ M)
    (hM : 3 ≤ finrank K M) (hT : 2 ≤ finrank K T)
    (hsupp : ∀ i, ∃ w ∈ T, w i ≠ 0) (hn : HasNoPointWords M T) :
    2 ≤ finrank K T - finrank K (conductor T M) := by
  apply two_le_conductor_boundary_of_restriction_finrank M T h1 _ hT hn
  have he : {i | ∃ w ∈ T, w i ≠ 0} = Set.univ := Set.eq_univ_of_forall hsupp
  rw [he, finrank_coordinateRestriction_univ]
  exact hM

end MMRank
