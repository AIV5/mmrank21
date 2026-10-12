module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Defs

@[expose] public section

/-! # Размерность пространства разделённых линейных отображений

Используется только невырожденность первого аргумента спаривания b:V×U→K.
Образ v,θ ↦ (u ↦ b(v,u)θ) считается без выбора тензорного базиса.
-/

namespace MMRank

open Module
open scoped BigOperators

variable {K U V Q : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

/-- Разделённое отображение u ↦ b(v,u)θ, линейное по v. -/
def separableMap (b : V →ₗ[K] U →ₗ[K] K) (θ : Q → K) :
    V →ₗ[K] U →ₗ[K] (Q → K) where
  toFun v := (b v).smulRight θ
  map_add' v w := by ext u q; simp [add_mul]
  map_smul' r v := by ext u q; simp [mul_assoc]

@[simp] theorem separableMap_apply (b : V →ₗ[K] U →ₗ[K] K)
    (θ : Q → K) (v : V) (u : U) (q : Q) :
    separableMap b θ v u q = b v u * θ q := rfl

variable [Fintype Q] [FiniteDimensional K U] [FiniteDimensional K V]

/-- Дополнительное фиксированное ненулевое направление для всего V даёт
dim V+(|Q|−1)dim E≤dim T. -/
theorem finrank_le_of_separable_maps_and_line (b : V →ₗ[K] U →ₗ[K] K)
    (hb : Function.Injective b) (E : Submodule K V)
    (T : Submodule K (U →ₗ[K] (Q → K))) (η : Q → K) (hη : η ≠ 0)
    (hline : ∀ v, separableMap b η v ∈ T)
    (hT : ∀ v ∈ E, ∀ θ : Q → K, separableMap b θ v ∈ T) :
    finrank K V + (Fintype.card Q - 1) * finrank K E ≤ finrank K T := by
  classical
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, η q₀ ≠ 0 := Function.ne_iff.mp hη
  let J := {q : Q // q ≠ q₀}
  let f : (V × (J → E)) →ₗ[K] (U →ₗ[K] (Q → K)) :=
    { toFun := fun v ↦ separableMap b η v.1 +
        ∑ q : J, separableMap b (Pi.single q.val 1) (v.2 q).val
      map_add' := by intros; ext u q; simp [Finset.sum_add_distrib]; ring
      map_smul' := by intros; ext u q; simp [Finset.mul_sum] }
  have hf (v : V × (J → E)) : f v ∈ T :=
    T.add_mem (hline _) (Submodule.sum_mem _ fun q _ ↦ hT _ (v.2 q).property _)
  have hzero : ∀ v, f v = 0 → v = 0 := by
    intro v hh
    have hfirst : v.1 = 0 := by
      apply hb
      ext u
      have hz := congrArg (fun g : U →ₗ[K] (Q → K) ↦ g u q₀) hh
      have hn (q : J) : q₀ ≠ q.val := Ne.symm q.property
      have hz' : b v.1 u * η q₀ = 0 := by
        simpa [f, Pi.single_apply, hn] using hz
      simpa using (mul_eq_zero.mp hz').resolve_right hq₀
    have hsecond : v.2 = 0 := by
      funext q
      apply Subtype.ext
      apply hb
      ext u
      have hz := congrArg (fun g : U →ₗ[K] (Q → K) ↦ g u q.val) hh
      have hs : (∑ c : J, if q = c then b (v.2 c).val u else 0) = b (v.2 q).val u := by
        rw [Finset.sum_eq_single q]
        · simp
        · intro c _ hc
          simp [Ne.symm hc]
        · simp
      have hz' : (∑ c : J, if q = c then b (v.2 c).val u else 0) = 0 := by
        simpa [f, hfirst, Pi.single_apply, ← Subtype.ext_iff] using hz
      simpa [hs] using hz'
    exact Prod.ext hfirst hsecond
  have hinj : Function.Injective (f.codRestrict T hf) := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hvw)
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  have hc : Fintype.card J = Fintype.card Q - 1 := by
    simp [J, Fintype.card_subtype_compl]
  simpa [Module.finrank_prod, Module.finrank_pi_fintype, hc] using h

end MMRank
