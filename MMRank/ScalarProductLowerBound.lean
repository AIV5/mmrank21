import MMRank.PartialProductTransport
import MMRank.CoordinateRestriction

namespace MMRank
open Matrix Module
variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

/-- δ независимых тестов при δ≥3 стоят
не менее3n+δ−3 членов. Сечение размерности3 гасит δ−3 выходных форм,
после чего применяется трёхсрезовая граница. Без разбора δ=3 и δ=4. -/
theorem partial_twoByTwo_dimension_lower [Nonempty N]
    (T : Submodule K (Matrix (Fin 2) (Fin 2) K)) (hT : 3 ≤ finrank K T)
    (a : I → Matrix (Fin 2) N K →ₗ[K] K) (b : I → Matrix N (Fin 2) K →ₗ[K] K)
    (c : I → Matrix (Fin 2) (Fin 2) K →ₗ[K] K)
    (h : ∀ C ∈ T, ∀ A B, trace (C * (A * B)) = ∑ i, (a i A * b i B) * c i C) :
    3 * Fintype.card N + finrank K T ≤ Fintype.card I + 3 := by
  classical
  let γ : T →ₗ[K] (I → K) := LinearMap.pi (fun i ↦ (c i).comp T.subtype)
  have hγ : Function.Injective γ := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro C hC
    have hz (i : I) : c i C.val = 0 := congrFun hC i
    apply Subtype.ext
    ext p q
    have hh := h C.val C.property (single q (Classical.arbitrary N) 1)
      (single (Classical.arbitrary N) p 1)
    simpa [Matrix.single_mul_single_same, Matrix.trace_mul_single, hz] using hh
  obtain ⟨U, G, hU, hG, hz⟩ := exists_subspace_annihilating_coordinates γ hγ 3 hT
  have hd : finrank K (U.map T.subtype) = 3 := (T.finrank_map_subtype_eq U).trans hU
  have hb := partial_twoByTwo_lower (U.map T.subtype) hd
    (fun i : ↥(Gᶜ) ↦ a i.val) (fun i : ↥(Gᶜ) ↦ b i.val)
    (fun i C ↦ c i.val C) (by
      rintro _ ⟨C, hC, rfl⟩ A B
      change trace (C.val * (A * B)) = _
      rw [h C.val C.property A B]
      apply Finset.sum_congr_set Gᶜ _ _
      · intro i hi; rfl
      · intro i hi
        rw [show c i C.val = 0 from hz C hC i (by simpa using hi), mul_zero])
  rw [Set.fintypeCard_eq_ncard] at hb
  have hc := G.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hc
  omega

end MMRank
