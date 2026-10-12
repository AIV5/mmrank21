module

public import MMRank.CrossTestRelations

@[expose] public section

/-! # Общий порождающий вектор отношений и векторные множители -/

namespace MMRank
open Matrix Module
open scoped Classical
variable {K I V Q : Type*} [Field K] [Fintype I]
  [AddCommGroup V] [Module K V]

/-- Если число векторов на единицу больше размерности их оболочки,
все отношения порождены одним ненулевым словом. -/
theorem exists_relation_generator_of_corank_one (v : I → V)
    (hv : finrank K (Submodule.span K (Set.range v)) + 1 = Fintype.card I) :
    ∃ w : I → K, w ≠ 0 ∧ (Fintype.linearCombination K v).ker = Submodule.span K {w} := by
  let L := Fintype.linearCombination K v
  have hh := L.finrank_range_add_finrank_ker
  rw [Fintype.range_linearCombination, Module.finrank_fintype_fun_eq_card] at hh
  have hd : finrank K L.ker = 1 := by omega
  have hn : L.ker ≠ ⊥ := by intro he; rw [he, finrank_bot] at hd; omega
  obtain ⟨w, hw, hw0⟩ := L.ker.ne_bot_iff.mp hn
  exact ⟨w, hw0, eq_span_singleton_of_mem_of_finrank_eq_one hd hw hw0⟩

/-- Векторные коэффициенты отношений факторизуются через один и тот
же порождающий вектор ядра. Множество координат Q может быть бесконечным. -/
theorem relation_vectors_factor (v : I → V) (w : I → K)
    (hw : (Fintype.linearCombination K v).ker = Submodule.span K {w})
    (c : I → Q → K) (hc : ∀ q, ∑ i, c i q • v i = 0) :
    ∃ p : Q → K, ∀ i, c i = w i • p := by
  have h (q : Q) : ∃ a : K, a • w = fun i ↦ c i q := by
    apply Submodule.mem_span_singleton.mp
    rw [← hw]
    exact hc q
  choose p hp using h
  refine ⟨p, ?_⟩
  intro i
  ext q
  have hh := congrFun (hp q) i
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hh.symm

end MMRank
