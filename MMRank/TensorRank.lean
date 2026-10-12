import MMRank.SpanConnected
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Сокращения тензоров и размерностная оценка присоединения

Нулевая сумма простых тензоров даёт ограничение суммы факторных рангов.
Ненулевое пересечение со старой тензорной оболочкой даёт оценку прироста.
-/

open scoped TensorProduct
open Module

namespace MMRank

variable {K ι X Y : Type*} [Field K]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- Сокращение первого фактора; для простого тензора это φ(x)y. -/
noncomputable def tensorContraction :
    X ⊗[K] Y →ₗ[K] (Module.Dual K X →ₗ[K] Y) :=
  (dualTensorHom K (Module.Dual K X) Y).comp
    (TensorProduct.map (Module.Dual.eval K X) LinearMap.id)

@[simp] theorem tensorContraction_tmul (x : X) (y : Y) (φ : Module.Dual K X) :
    tensorContraction (x ⊗ₜ[K] y) φ = φ x • y := rfl

theorem tensorContraction_injective [FiniteDimensional K X] :
    Function.Injective (tensorContraction (K := K) (X := X) (Y := Y)) := by
  let e := (TensorProduct.congr (Module.evalEquiv K X) (LinearEquiv.refl K Y)).trans
    (dualTensorHomEquiv K (Module.Dual K X) Y)
  exact e.injective

/-- Любой ненулевой тензор обнаруживается сокращением по первому фактору. -/
theorem exists_tensorContraction_ne_zero [FiniteDimensional K X]
    {t : X ⊗[K] Y} (ht : t ≠ 0) :
    ∃ φ : Module.Dual K X, tensorContraction t φ ≠ 0 := by
  by_contra! h
  apply ht
  apply tensorContraction_injective
  ext φ
  simpa using h φ

/-- Отображение всех оценок на конечном семействе имеет ранг его оболочки. -/
theorem finrank_range_familyEvaluation [Fintype ι] (y : ι → Y) :
    finrank K (LinearMap.pi (fun i ↦ (Module.Dual.eval K Y) (y i))).range =
      finrank K (Submodule.span K (Set.range y)) := by
  classical
  let f := Fintype.linearCombination K y
  let e := (Pi.basisFun K ι).dualBasis.equivFun
  have he : (LinearMap.pi (fun i ↦ (Module.Dual.eval K Y) (y i))) =
      e.toLinearMap.comp f.dualMap := by
    ext φ i
    simp [e, Basis.equivFun_apply, Basis.dualBasis_repr, f,
      Fintype.linearCombination_apply, Pi.basisFun_apply]
  rw [he, LinearMap.range_comp]
  rw [← (Submodule.equivMapOfInjective e.toLinearMap e.injective f.dualMap.range).finrank_eq]
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Fintype.range_linearCombination]

/-- Нулевая сумма простых тензоров ограничивает сумму факторных рангов.
Ненулевость слагаемых и связность здесь не требуются. -/
theorem finrank_factors_le_card_of_sum_tmul_eq_zero [Fintype ι]
    (x : ι → X) (y : ι → Y) (h : (∑ i, x i ⊗ₜ[K] y i) = 0) :
    finrank K (Submodule.span K (Set.range x)) +
      finrank K (Submodule.span K (Set.range y)) ≤ Fintype.card ι := by
  let f := Fintype.linearCombination K x
  let g := LinearMap.pi (fun i ↦ (Module.Dual.eval K Y) (y i))
  have hgf : g.range ≤ f.ker := by
    rintro _ ⟨φ, rfl⟩
    change (∑ i, φ (y i) • x i) = 0
    have hh := congrArg (fun t : X ⊗[K] Y ↦
      tensorContraction (TensorProduct.comm K X Y t) φ) h
    simpa only [map_sum, TensorProduct.comm_tmul, map_zero,
      LinearMap.sum_apply, tensorContraction_tmul, LinearMap.zero_apply] using hh
  have hr := f.finrank_range_add_finrank_ker
  have hd := Submodule.finrank_mono hgf
  rw [finrank_range_familyEvaluation] at hd
  rw [Fintype.range_linearCombination, Module.finrank_fintype_fun_eq_card] at hr
  omega

/-- Независимые ненулевые масштабы не меняют оболочку семейства. -/
theorem span_range_smul_eq_of_ne_zero (x : ι → X) (c : ι → K) (hc : ∀ i, c i ≠ 0) :
    Submodule.span K (Set.range (fun i ↦ c i • x i)) =
      Submodule.span K (Set.range x) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hh := Submodule.smul_mem
      (Submodule.span K (Set.range (fun i ↦ c i • x i))) (c i)⁻¹
      (Submodule.subset_span (Set.mem_range_self i))
    simpa [smul_smul, hc i] using hh

/-- Размерность новых направлений относительно заданного подпространства. -/
theorem finrank_map_mkQ_add [FiniteDimensional K X] (A B : Submodule K X) :
    finrank K (B.map A.mkQ) + finrank K A = finrank K ↥(A ⊔ B) := by
  have h := (A.mkQ.domRestrict B).finrank_range_add_finrank_ker
  have hk : (A.mkQ.domRestrict B).ker = A.comap B.subtype := by
    ext x
    simp
  have hr : (A.mkQ.domRestrict B).range = B.map A.mkQ := by
    rw [LinearMap.domRestrict, LinearMap.range_comp, Submodule.range_subtype]
  rw [hk, hr] at h
  have hi : (A ⊓ B).comap B.subtype = A.comap B.subtype := by ext x; simp
  have he := (Submodule.comapSubtypeEquivOfLe (inf_le_right : A ⊓ B ≤ B)).finrank_eq
  rw [hi] at he
  rw [he] at h
  have hs := Submodule.finrank_sup_add_finrank_inf_eq A B
  omega

theorem tensorContraction_mem_span (x : ι → X) (y : ι → Y) (s : Set ι)
    {t : X ⊗[K] Y} (ht : t ∈ Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' s))
    (φ : Module.Dual K X) : tensorContraction t φ ∈ Submodule.span K (y '' s) := by
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
  | smul a b _ hb => simpa using Submodule.smul_mem _ a hb

theorem tensor_mkQ_eq_zero_of_mem_span (x : ι → X) (y : ι → Y) (s : Set ι)
    {t : X ⊗[K] Y} (ht : t ∈ Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' s)) :
    TensorProduct.map (Submodule.span K (x '' s)).mkQ (LinearMap.id : Y →ₗ[K] Y) t = 0 := by
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    have hi' : (Submodule.span K (x '' s)).mkQ (x i) = 0 := by
      simpa using (Submodule.subset_span ⟨i, hi, rfl⟩ : x i ∈ Submodule.span K (x '' s))
    simp [hi']
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b _ hb => simp [hb]

/-- Оценка прироста двух факторных оболочек при ненулевом соединении.
Коэффициенты нового семейства должны быть ненулевыми; его независимость не нужна. -/
theorem tensor_bridge_factor_growth [FiniteDimensional K X] [FiniteDimensional K Y]
    {κ : Type*} [Fintype κ] (x : ι → X) (y : ι → Y) (s : Set ι)
    (u : κ → X) (v : κ → Y) (c : κ → K) (hc : ∀ i, c i ≠ 0)
    (hw : (∑ i, c i • (u i ⊗ₜ[K] v i)) ≠ 0)
    (hmem : (∑ i, c i • (u i ⊗ₜ[K] v i)) ∈
      Submodule.span K ((fun i ↦ x i ⊗ₜ[K] y i) '' s)) :
    finrank K ↥(Submodule.span K (x '' s) ⊔ Submodule.span K (Set.range u)) +
      finrank K ↥(Submodule.span K (y '' s) ⊔ Submodule.span K (Set.range v)) + 1 ≤
      finrank K (Submodule.span K (x '' s)) +
        finrank K (Submodule.span K (y '' s)) + Fintype.card κ := by
  let A := Submodule.span K (x '' s)
  let B := Submodule.span K (y '' s)
  let U := Submodule.span K (Set.range u)
  let V := Submodule.span K (Set.range v)
  have hz := tensor_mkQ_eq_zero_of_mem_span x y s hmem
  have hz' : (∑ i, (c i • A.mkQ (u i)) ⊗ₜ[K] v i) = 0 := by
    simpa only [map_sum, map_smul, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.smul_tmul'] using hz
  have hr := finrank_factors_le_card_of_sum_tmul_eq_zero
    (fun i ↦ c i • A.mkQ (u i)) v hz'
  rw [span_range_smul_eq_of_ne_zero _ c hc] at hr
  have hmap : Submodule.span K (Set.range (fun i ↦ A.mkQ (u i))) = U.map A.mkQ := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hmap] at hr
  obtain ⟨φ, hφ⟩ := exists_tensorContraction_ne_zero hw
  have hb := tensorContraction_mem_span x y s hmem φ
  have hv : tensorContraction (∑ i, c i • (u i ⊗ₜ[K] v i)) φ ∈ V := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      tensorContraction_tmul]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hpos : 1 ≤ finrank K ↥(B ⊓ V) := by
    rw [Submodule.one_le_finrank_iff]
    intro hh
    apply hφ
    have hm : tensorContraction (∑ i, c i • (u i ⊗ₜ[K] v i)) φ ∈ B ⊓ V := ⟨hb, hv⟩
    simpa only [hh, Submodule.mem_bot] using hm
  have hA := finrank_map_mkQ_add A U
  have hB := Submodule.finrank_sup_add_finrank_inf_eq B V
  change finrank K ↥(A ⊔ U) + finrank K ↥(B ⊔ V) + 1 ≤
    finrank K A + finrank K B + Fintype.card κ
  change finrank K (U.map A.mkQ) + finrank K V ≤ Fintype.card κ at hr
  omega

end MMRank
