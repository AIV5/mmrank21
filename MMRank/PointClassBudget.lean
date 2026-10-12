import MMRank.ConductorLengthBounds

/-! # Бюджеты первого класса без ненулевости его тестового пространства -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Три бюджета класса для333 над произвольным полем. Длина и
ненулевость внутреннего тестового пространства не ограничиваются. -/
theorem point_class_budget (alg : ExactAlgorithm K P Q S I)
    (hP : Fintype.card P = 3) (hQ : Fintype.card Q = 3) (hS : Fintype.card S = 3)
    (p : P → K) (hp : p ≠ 0) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p) :
    let δ := finrank K (coordinateSection K alg.toCoefficients.gamma.range G)
    let d := finrank K (alg.reflect.toCoefficients.externalPairSum (Submodule.span K {p}) G).range
    3 * δ ≤ G.ncard ∧ 15 ≤ d ∧ d + 3 ≤ (Gᶜ).ncard + δ := by
  classical
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  let F : Submodule K (P → K) := Submodule.span K {p}
  have hF : finrank K F = 1 := finrank_span_singleton hp
  have hG (i : I) (hi : i ∈ G) : alg.reflect.U i ∈ matricesInto (S := Q) F := by
    apply (transpose_mem_matricesInto_span_iff p (alg.U i)).mpr
    exact hspan (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hmass := alg.supportedTest_mass_le_card p hp G hspan
  rw [hQ] at hmass
  have he := (alg.supportedTestRadicalEquiv p hp G hspan).finrank_eq
  have hbudget := alg.reflect.exterior_pair_budget F G hG
  rw [hF, hS, mul_one, ← he] at hbudget
  obtain ⟨n, ⟨rect⟩, hn⟩ := alg.reflect.exists_rectangular_compression F G hG
  have hquot : finrank K ((P → K) ⧸ F) = 2 := by
    have hh := F.finrank_quotient_add_finrank
    rw [hF, Module.finrank_fintype_fun_eq_card, hP] at hh
    omega
  have hr := rect.length_bound_three_by_two hQ (by simpa using hquot) (by omega)
  simp only [hS, Fintype.card_fin] at hr
  have h15 : 15 ≤ n := by omega
  exact ⟨hmass, hn ▸ h15, hbudget⟩

/-- Вместимость любого первого столбцового класса при длине≤20.
Наличие точечного слова или вообще ненулевого теста не требуется. -/
theorem point_class_capacity (alg : ExactAlgorithm K P Q S I)
    (hP : Fintype.card P = 3) (hQ : Fintype.card Q = 3) (hS : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (p : P → K) (hp : p ≠ 0) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p) :
    G.ncard ≤ 3 ∧ finrank K (coordinateSection K alg.toCoefficients.gamma.range G) ≤ 1 := by
  have hb := alg.point_class_budget hP hQ hS p hp G hspan
  have hc := G.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hc
  dsimp only at hb
  omega

/-- Та же вместимость для общего строкового направления первых матриц;
цикл переносит её на любой коэффициентный столбец. -/
theorem row_class_card_le_three (alg : ExactAlgorithm K P Q S I)
    (hP : Fintype.card P = 3) (hQ : Fintype.card Q = 3) (hS : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (q : Q → K) (hq : q ≠ 0) (G : Set I)
    (hG : ∀ i ∈ G, alg.U i ∈ matricesInto (S := P) (Submodule.span K {q})) :
    G.ncard ≤ 3 := by
  apply (alg.reflect.point_class_capacity hQ hP hS hl q hq G ?_).1
  apply Submodule.span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  exact (transpose_mem_matricesInto_span_iff q (alg.U i).transpose).mp
    (by simpa only [Matrix.transpose_transpose] using hG i hi)

end MMRank.ExactAlgorithm
