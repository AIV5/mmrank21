import MMRank.FixedColumnBasis
import MMRank.SubspaceMatrixChart

/-! # Базисы ранга один в матричных гиперплоскостях

Нулевые пары скалярной билинейной формы определяют любую подчинённую форму
с произвольным модульным выходом. Двойственное отделение даёт порождение
матричного ядра его rank1-членами без разбора ранга нормали.
Basis.ofSpan/indexEquiv сохраняют исходный тип индексов; готовые матричная
ретракция и эквивалентность прообраза переносят базис в фиксированный образ.
Поле произвольное, включая конечные поля; IsAlgClosed не требуется.
-/
noncomputable section
namespace MMRank
variable {K E F W : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup W] [Module K W]

open Module

/-- Подпространство коразмерности1 есть ядро ненулевой формы.
Использует готовое отделение подпространства и размерность ядра формы. -/
theorem exists_dual_kernel_of_finrank_add_one {R V : Type*} [DivisionRing R]
    [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    (H : Submodule R V) (hd : finrank R H + 1 = finrank R V) :
    ∃ φ : V →ₗ[R] R, φ ≠ 0 ∧ H = φ.ker := by
  have ht : H < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    rw [he, finrank_top] at hd
    omega)
  obtain ⟨φ, hφ, hle⟩ := H.exists_le_ker_of_lt_top ht
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  exact ⟨φ, hφ, Submodule.eq_of_le_of_finrank_eq hle (by omega)⟩

/-- Порождающее множество содержит базис с тем же типом индексов,
что и заданный базис. Достаточно тела; конечномерность не нужна. -/
theorem exists_basis_in_spanning_set {R V J : Type*} [DivisionRing R]
    [AddCommGroup V] [Module R V] (b₀ : Basis J R V)
    (s : Set V) (hs : Submodule.span R s = ⊤) :
    ∃ b : Basis J R V, ∀ i, b i ∈ s := by
  let b := Basis.ofSpan hs.ge
  let e := b.indexEquiv b₀
  refine ⟨b.reindex e, fun i ↦ ?_⟩
  simpa only [Basis.reindex_apply] using (Basis.ofSpan_subset hs.ge ⟨e.symm i, rfl⟩)

section Matrices
open Matrix Module
variable {P Q : Type*} [Fintype P] [Fintype Q]

end Matrices
end MMRank
