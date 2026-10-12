module

public import MMRank.FullColumnTriple
public import MMRank.CrossTestRelations

@[expose] public section

/-! # Малые классы первых коэффициентов

Общая вместимость
поддержанного теста и размерная специализация используют существующий бюджет класса, без расщепления тестового пучка.
-/

namespace MMRank
open Matrix Module
open scoped Classical
variable {K P Q I S : Type*} [Field K]
  [Fintype P] [Fintype Q]

/-- При длине≤20 общий строковый класс первых коэффициентов не может
иметь три индекса, если их столбцы лежат в собственном подпространстве.
Нормировка, минимальность и общность точки не требуются. -/
theorem ExactAlgorithm.proper_column_fixed_row_card_le_two
    [Fintype I] [Fintype S]
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (F : Submodule K (P → K))
    (hF : finrank K F < Fintype.card P) (G : Set I)
    (hcols : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F)
    (r : Q → K) (hr : r ≠ 0)
    (hrows : ∀ i ∈ G, alg.U i ∈ matricesInto (S := P) (Submodule.span K {r})) :
    G.ncard ≤ 2 := by
  let : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  have hc : Submodule.span K (alg.reflect.U '' G) ≤ fixedColumnSpace (Q := P) r := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact (transpose_mem_matricesInto_span_iff r (alg.U i).transpose).mp
      (by simpa only [transpose_transpose] using hrows i hi)
  have hb := alg.reflect.point_class_budget hq hp hs r hr G hc
  have hcard := G.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hcard
  by_contra! hg
  have hn : coordinateSection K alg.reflect.toCoefficients.gamma.range G ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hb
    dsimp only at hb
    omega
  have hfull := alg.reflect.fixedColumn_span_eq_of_section_ne_bot r G hc hn
  obtain ⟨x, hx⟩ := exists_dotProduct_eq_one r hr
  have he := row_projection_span_eq_top alg.reflect.U G r x hx (by rw [hfull])
  have hle : Submodule.span K ((fun i ↦ x ᵥ* alg.reflect.U i) '' G) ≤ F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact (mem_matricesInto F _).mp (hcols i hi) ⟨x, rfl⟩
  rw [he] at hle
  have ht : F = ⊤ := top_le_iff.mp hle
  rw [ht, finrank_top, Module.finrank_fintype_fun_eq_card] at hF
  exact (lt_irrefl _ hF)

/-- Ненулевой поддержанный тест не может иметь весь носитель в одном
столбцовом классе мощности меньше внутренней размерности. -/
theorem ExactAlgorithm.supported_test_not_small_fixed_column
    [Fintype I] [Fintype S] [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (G : Set I)
    (C : Matrix P S K) (hC : C ≠ 0)
    (hCG : C ∈ alg.toCoefficients.supportedTests G)
    (p : P → K) (hp : p ≠ 0)
    (hcard : {i ∈ G | alg.U i ∈ fixedColumnSpace (Q := Q) p}.ncard < Fintype.card Q) :
    ¬ (∀ i ∈ G, alg.toCoefficients.gamma C i ≠ 0 → alg.U i ∈ fixedColumnSpace p) := by
  intro h
  let H := {i ∈ G | alg.U i ∈ fixedColumnSpace (Q := Q) p}
  have hw : alg.toCoefficients.gamma C ∈ coordinateSection K alg.toCoefficients.gamma.range H := by
    refine mem_coordinateSection.mpr ⟨⟨C, rfl⟩, ?_⟩
    intro i hi
    by_cases hiG : i ∈ G
    · by_contra hn
      exact hi ⟨hiG, h i hiG hn⟩
    · exact (Coefficients.mem_supportedTests _ _ _).mp hCG i hiG
  have hn : alg.toCoefficients.gamma C ≠ 0 := by
    intro hz
    exact hC (alg.gamma_injective (by simpa only [map_zero] using hz))
  have hd : 1 ≤ finrank K (coordinateSection K alg.toCoefficients.gamma.range H) :=
    Submodule.one_le_finrank_iff.mpr (fun hz ↦ hn (by simpa only [hz, Submodule.mem_bot] using hw))
  have hb := alg.supportedTest_mass_le_card p hp H
    (Submodule.span_le.mpr (by rintro _ ⟨i, hi, rfl⟩; exact hi.2))
  have hle := (Nat.mul_le_mul_left (Fintype.card Q) hd).trans hb
  simp only [mul_one] at hle
  exact (not_lt_of_ge hle) hcard

end MMRank
