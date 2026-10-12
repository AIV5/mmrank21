import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Set.Card

/-! # Замещение выбранных независимых первых форм над произвольным полем -/

namespace MMRank
open Module
variable {K X Y I : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [FiniteDimensional K Y] [Fintype I]

/-- Если первые формы различают вторую группу переменных, можно погасить
dim Y различных слагаемых подстановкой y=Lx. Поле произвольно; X может
быть бесконечномерным, а Y нулевым. -/
theorem exists_linear_substitution (a : I → (X × Y) →ₗ[K] K)
    (ha : ∀ y : Y, (∀ i, a i (0, y) = 0) → y = 0) :
    ∃ (G : Set I) (L : X →ₗ[K] Y), G.ncard = finrank K Y ∧
      ∀ i ∈ G, ∀ x, a i (x, L x) = 0 := by
  classical
  let v : I → Module.Dual K Y := fun i ↦ (a i).comp (LinearMap.inr K X Y)
  obtain ⟨J, idx, hi, hs, hlin⟩ := exists_linearIndependent' K v
  let : Finite J := Finite.of_injective idx hi
  let : Fintype J := Fintype.ofFinite J
  let T : Y →ₗ[K] (J → K) := LinearMap.pi (fun j ↦ v (idx j))
  have hT : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro y hy
    apply ha y
    intro i
    have hz : ∀ f ∈ Submodule.span K (Set.range (v ∘ idx)), f y = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨j, rfl⟩ := hz
          exact congrFun hy j
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c z _ hz => simp [hz]
    exact hz (v i) (by rw [hs]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hlo := LinearMap.finrank_le_finrank_of_injective hT
  have hhi := hlin.fintype_card_le_finrank
  have hdim : finrank K Y = Fintype.card J := by
    simp only [Module.finrank_pi] at hlo
    rw [Subspace.dual_finrank_eq] at hhi
    omega
  let e : Y ≃ₗ[K] (J → K) := LinearEquiv.ofBijective T
    ⟨hT, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simpa using hdim)).mp hT⟩
  let A : X →ₗ[K] (J → K) := LinearMap.pi (fun j ↦ (a (idx j)).comp (LinearMap.inl K X Y))
  let L : X →ₗ[K] Y := -(e.symm.toLinearMap.comp A)
  refine ⟨Set.range idx, L, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card]
    exact hdim.symm
  · rintro _ ⟨j, rfl⟩ x
    have he : a (idx j) (0, e.symm (A x)) = a (idx j) (x, 0) :=
      congrFun (e.apply_symm_apply (A x)) j
    have hh := (a (idx j)).map_sub (x, 0) (0, e.symm (A x))
    simpa [L, he] using hh

/-- Замещение dim Y первых форм плюс инъективность второй развёртки
после любой линейной подстановки y=Lx дают dim Y+dim V.
Выход может зависеть от y; независимость от y не предполагается. -/
theorem bilinear_length_bound_of_substitution_graph {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (a : I → (X × Y) →ₗ[K] K) (b : I → V →ₗ[K] K) (c : I → W)
    (f : X × Y → V → W)
    (ha : ∀ y : Y, (∀ i, a i (0, y) = 0) → y = 0)
    (hf : ∀ x y v, f (x, y) v = ∑ i, (a i (x, y) * b i v) • c i)
    (hsep : ∀ L : X →ₗ[K] Y, ∀ v, (∀ x, f (x, L x) v = 0) → v = 0) :
    finrank K Y + finrank K V ≤ Fintype.card I := by
  classical
  obtain ⟨G, L, hG, hL⟩ := exists_linear_substitution a ha
  let T : V →ₗ[K] (↥(Gᶜ) → K) := LinearMap.pi (fun i ↦ b i.val)
  have hi : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply hsep L v
    intro x
    rw [hf x (L x) v]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hiG : i ∈ G
    · rw [hL i hiG x, zero_mul, zero_smul]
    · have hb : b i v = 0 := congrFun hv ⟨i, hiG⟩
      rw [hb, mul_zero, zero_smul]
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  rw [Module.finrank_pi] at hd
  have hc := G.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hc
  have he : Fintype.card ↥(Gᶜ) = Gᶜ.ncard := Nat.card_eq_fintype_card.symm
  rw [he] at hd
  omega

/-- Если сохраняемые выходы не зависят от y, достаточно их исходной
инъективной второй развёртки. Прежняя сигнатура сохранена. -/
theorem bilinear_length_bound_of_substitution {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W]
    (a : I → (X × Y) →ₗ[K] K) (b : I → V →ₗ[K] K) (c : I → W)
    (f : X → V → W)
    (ha : ∀ y : Y, (∀ i, a i (0, y) = 0) → y = 0)
    (hf : ∀ x y v, f x v = ∑ i, (a i (x, y) * b i v) • c i)
    (hsep : ∀ v, (∀ x, f x v = 0) → v = 0) :
    finrank K Y + finrank K V ≤ Fintype.card I :=
  bilinear_length_bound_of_substitution_graph a b c (fun z v ↦ f z.1 v)
    ha hf (fun _ ↦ hsep)

end MMRank
