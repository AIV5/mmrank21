module

public import MMRank.ResidualCoefficientCode
public import MMRank.RankOneIdentityBasis

@[expose] public section

/-! # Оболочка среза как единица плюс образ строк ядра
Прямое дополнение без секции F.
-/
noncomputable section
namespace MMRank
open Matrix Module
variable {K E I Q : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Fintype Q] [DecidableEq Q]

omit [FiniteDimensional K E] in
/-- Порождающие строки ядра восстанавливают всю оболочку срезов. -/
theorem span_trace_slice_eq_one_sup_range
    (A : I → Matrix Q Q K) (c : I → K) (μ : I → E)
    (hμ : Submodule.span K (Set.range μ) = ⊤) (Z : E →ₗ[K] Matrix Q Q K)
    (hA : ∀ i, A i = c i • 1 + Z (μ i))
    (h1 : (1 : Matrix Q Q K) ∈ Submodule.span K (Set.range A)) :
    Submodule.span K (Set.range A) = Submodule.span K {1} ⊔ Z.range := by
  classical
  let M := Submodule.span K (Set.range A)
  have hZ : Z.range ≤ M := by
    have hs : Submodule.span K (Set.range (fun i ↦ Z (μ i))) = Z.range := by
      rw [Set.range_comp', ← Submodule.map_span, hμ, Submodule.map_top]
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change Z (μ i) ∈ M
    have he : Z (μ i) = A i - c i • (1 : Matrix Q Q K) := by rw [hA]; abel
    rw [he]
    exact M.sub_mem (Submodule.subset_span (Set.mem_range_self i)) (M.smul_mem _ h1)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hA]
    exact Submodule.mem_sup.mpr ⟨c i • 1, Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton 1)), Z (μ i), ⟨μ i, rfl⟩, rfl⟩
  · exact sup_le (Submodule.span_le.mpr (by simpa using h1)) hZ

/-- Занулённая диагональная координата отделяет образ Z от скалярной единицы. -/
theorem finrank_one_sup_range_of_diagonal_zero [Nonempty Q]
    (Z : E →ₗ[K] Matrix Q Q K) (q₀ : Q) (hz : ∀ x, Z x q₀ q₀ = 0) :
    finrank K (Submodule.span K {1} ⊔ Z.range : Submodule K (Matrix Q Q K)) =
      1 + finrank K Z.range := by
  have hi : Submodule.span K {1} ⊓ Z.range = ⊥ := by
    apply eq_bot_iff.mpr
    intro A hA
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hA.1
    obtain ⟨x, hx⟩ := hA.2
    have hcx := hc.trans hx.symm
    have he := congrArg (fun A : Matrix Q Q K ↦ A q₀ q₀) hcx
    have hc0 : c = 0 := by simpa [hz x] using he
    simpa [hc0] using hc.symm
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {1}) Z.range
  rw [hi, finrank_bot, add_zero, finrank_span_singleton one_ne_zero] at hd
  exact hd

omit [DecidableEq Q] in
/-- Простые генераторы порождают ту же оболочку внутри подтипа. -/
theorem span_rank_one_subtype_eq_top_of_spanning_family
    (A : I → Matrix Q Q K) (hA : ∀ i, (A i).rank ≤ 1) :
    let M := Submodule.span K (Set.range A)
    Submodule.span K {B : M | B.val.rank ≤ 1} = ⊤ := by
  dsimp only
  let M := Submodule.span K (Set.range A)
  have hm (i : I) : A i ∈ M := Submodule.subset_span (Set.mem_range_self i)
  have hg := (Submodule.span_range_subtype_eq_top_iff M hm).mpr rfl
  apply top_le_iff.mp
  rw [← hg]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hA i)

end MMRank
