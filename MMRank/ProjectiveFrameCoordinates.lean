import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic

/-! # Ненулевые координаты дополнительного направления репера -/
namespace MMRank
open Module
variable {K V n : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq n]

/-- Если замена любого одного базисного вектора на x сохраняет
независимость, все координаты x ненулевые. Индексный тип произволен. -/
theorem basis_repr_ne_zero_of_independent_updates (b : Basis n K V) (x : V)
    (h : ∀ i, LinearIndependent K (Function.update b i x)) :
    ∀ i, b.repr x i ≠ 0 := by
  intro i hi
  have hx : x ∈ Submodule.span K (b '' ({i}ᶜ : Set n)) := by
    apply b.mem_span_image.mpr
    intro j hj
    have hj' : b.repr x j ≠ 0 := Finsupp.mem_support_iff.mp hj
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro he
    subst j
    exact hj' hi
  have he : Function.update b i x '' ({i}ᶜ : Set n) = b '' ({i}ᶜ : Set n) := by
    apply Set.image_congr
    intro j hj
    exact Function.update_of_ne (by simpa using hj) x b
  have hh := (h i).notMem_span_image (s := ({i}ᶜ : Set n)) (x := i) (by simp)
  rw [he] at hh
  exact hh (by simpa using hx)

/-- Любые n из n+1 направлений независимы: первые n образуют базис,
а последнее имеет все координаты ненулевыми. -/
theorem exists_basis_of_projective_frame (d : ℕ) [FiniteDimensional K V]
    (hd : finrank K V = d) (p : Fin (d + 1) → V)
    (h : ∀ e : Fin d → Fin (d + 1), Function.Injective e → LinearIndependent K (p ∘ e)) :
    ∃ b : Basis (Fin d) K V, (∀ i, b i = p i.castSucc) ∧
      ∀ i, b.repr (p (Fin.last d)) i ≠ 0 := by
  classical
  have hbase := h Fin.castSucc (Fin.castSucc_injective d)
  let b := basisOfLinearIndependentOfCardEqFinrank' (p ∘ Fin.castSucc) hbase (by simpa using hd.symm)
  have hb (i) : b i = p i.castSucc := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', Function.comp_apply]
  refine ⟨b, hb, basis_repr_ne_zero_of_independent_updates b _ ?_⟩
  intro i
  let e : Fin d → Fin (d + 1) := Function.update Fin.castSucc i (Fin.last d)
  have he : Function.Injective e := by
    intro j k hjk
    by_cases hj : j = i <;> by_cases hk : k = i
    · exact hj.trans hk.symm
    · subst j
      have hh : Fin.last d = k.castSucc := by simpa [e, hk] using hjk
      exact (Fin.castSucc_ne_last k hh.symm).elim
    · subst k
      simp [e, hj] at hjk
    · simpa [e, hj, hk] using hjk
  have hh := h e he
  have hv : p ∘ e = Function.update b i (p (Fin.last d)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [e]
    · simp [e, hj, hb]
  rwa [hv] at hh

end MMRank
