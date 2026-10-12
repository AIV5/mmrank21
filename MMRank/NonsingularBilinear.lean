import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Билинейные отображения без делителей нуля над замкнутым полем

Общий аргумент собственного вектора исключает постоянные ядро и
уничтожающую форму в равных размерностях n≥3 при рангах ≥n−1.
Выбор матричного базиса не требуется.
-/

namespace MMRank
open Module

/-- Над алгебраически замкнутым полем билинейное отображение без делителей
нуля в равномерный выход допускает лишь одномерный второй аргумент. -/
theorem finrank_right_le_one_of_nonsingular_bilinear
    {K T U V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup T] [Module K T] [FiniteDimensional K T] [Nontrivial T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hTV : finrank K T = finrank K V)
    (B : T →ₗ[K] (U →ₗ[K] V))
    (hnz : ∀ t u, B t u = 0 → t = 0 ∨ u = 0) : finrank K U ≤ 1 := by
  by_contra hn
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank K U)
  obtain ⟨u, hu⟩ : ∃ u : U, u ≠ 0 := by
    exact exists_ne 0
  let f := B.flip u
  have hi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro t ht
    exact (hnz t u ht).resolve_right hu
  let e := LinearEquiv.ofBijective f
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hTV).mp hi⟩
  have hspan : Submodule.span K {u} ≠ (⊤ : Submodule K U) := by
    intro hh
    have := finrank_span_singleton (K := K) hu
    rw [hh, finrank_top] at this
    omega
  obtain ⟨v, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hspan)
  have hvspan : v ∉ Submodule.span K {u} := hv.2
  let g := e.symm.toLinearMap.comp (B.flip v)
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue g
  obtain ⟨t, ht⟩ := ha.exists_hasEigenvector
  have heig : g t = a • t := ht.apply_eq_smul
  have hb : B t v = a • B t u := by
    have het : e t = B t u := rfl
    have hh := congrArg e heig
    simpa only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_smul, het, LinearMap.flip_apply] using hh
  have hz : B t (v - a • u) = 0 := by simp [map_sub, map_smul, hb]
  have hvu := (hnz t (v - a • u) hz).resolve_left ht.2
  apply hvspan
  rw [sub_eq_zero.mp hvu]
  exact Submodule.smul_mem _ a (Submodule.subset_span (by simp))

end MMRank
