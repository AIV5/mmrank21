import MMRank.LinearRankSum
import Mathlib.LinearAlgebra.DFinsupp

/-! # Цена независимых представлений одного выхода
-/
namespace MMRank
open Module
variable {K E L J : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [AddCommGroup L] [Module K L] [FiniteDimensional K E] [FiniteDimensional K L]
  [Fintype J] [Nonempty J]

/-- k независимых представлений оплачивают k−1 копий общего выхода ядром F. -/
theorem disjoint_output_span_kernel_budget (F : E →ₗ[K] L)
    (N : J → Submodule K E) (hN : iSupIndep N) (B : Submodule K L)
    (hB : ∀ j, B ≤ (N j).map F) :
    Fintype.card J * finrank K B ≤ finrank K F.ker + finrank K B := by
  classical
  let T (j : J) := N j ⊓ B.comap F
  have hT : iSupIndep T := hN.mono (fun _ ↦ inf_le_left)
  have hm (j : J) : (T j).map F = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hB j hy
      exact ⟨x, ⟨hx, by simpa [hxy] using hy⟩, hxy⟩
  let g : (∀ j, T j) →ₗ[K] E :=
    { toFun x := ∑ j, (x j).val
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  have hg : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero T).mp hT
      Finset.univ (fun j ↦ (x j).val) (fun j _ ↦ (x j).property) hx
    apply funext
    intro j
    exact Subtype.ext (hz j (Finset.mem_univ j))
  let f := F.comp g
  have hf : f.range = B := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change F (∑ j, (x j).val) ∈ B
      rw [map_sum]
      exact B.sum_mem (fun j _ ↦ (x j).property.2)
    · intro y hy
      let j : J := Classical.arbitrary J
      obtain ⟨x, hx, hxy⟩ := show y ∈ (T j).map F from (hm j).symm ▸ hy
      refine ⟨Pi.single j ⟨x, hx⟩, ?_⟩
      change F (∑ k, ((Pi.single j ⟨x, hx⟩ : ∀ k, T k) k).val) = y
      have hs : (∑ k, ((Pi.single j ⟨x, hx⟩ : ∀ k, T k) k).val) = x := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [Pi.single_eq_of_ne hk]
        · simp
      rw [hs]
      exact hxy
  let e : f.ker →ₗ[K] F.ker :=
    (g.comp f.ker.subtype).codRestrict F.ker (fun x ↦ x.property)
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact hg (congrArg Subtype.val hxy)
  have hk := LinearMap.finrank_le_finrank_of_injective he
  have hr := f.finrank_range_add_finrank_ker
  have ht (j : J) : finrank K B ≤ finrank K (T j) := by
    have hh := (F.domRestrict (T j)).finrank_range_le
    rw [LinearMap.range_domRestrict] at hh
    rwa [hm] at hh
  have hd : Fintype.card J * finrank K B ≤ finrank K (∀ j, T j) := by
    rw [Module.finrank_pi_fintype]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset J)) (fun j _ ↦ ht j)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using hh
  rw [hf] at hr
  omega

end MMRank
