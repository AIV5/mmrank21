import MMRank.ResidualRayOutputBudget
import MMRank.QuadraticThreeRay

/-! # Короткий хвост реконструкции простых срезов

Пять независимых тестов, не более
трёх сепараторов и не более четырёх центров дают противоречие.
Классификация срезов остаётся отдельным входным сертификатом.
-/
namespace MMRank
open Module Submodule
open scoped BigOperators Classical

variable {K L I : Type*} [Field K] [AddCommGroup L] [Module K L]
  [FiniteDimensional K L] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Независимые выходы обязательно имеют разные центры. -/
theorem ThreeRayCover.center_ne_of_linearIndependent_outputs
    {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {μ : I → E} {s : Finset I} {C D : Submodule K E} (H : ThreeRayCover μ s C) (G : ThreeRayCover μ s D)
    (hE : finrank K E = 3) (F : (I → K) →ₗ[K] L) (hker : finrank K F.ker ≤ 3)
    (t u : L) (hli : LinearIndependent K ![t, u])
    (ht : ∀ a, t ∈ H.activeOutput F a) (hu : ∀ a, u ∈ G.activeOutput F a) : C ≠ D := by
  intro he
  subst D
  exact H.not_linearIndependent_outputs_of_same_center G hE F hker t u ht hu hli

/-- Сертификаты «хороший центр или плохой сепаратор» несовместимы с пятью
базисными выходами при ядре размерности≤3 и восьми направлениях μ. -/
theorem residual_ray_good_bad_contradiction
    (b : Basis (Fin 5) K L) (F : (I → K) →ₗ[K] L) (hker : finrank K F.ker ≤ 3)
    (μ : I → Fin 3 → K)
    (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hcard : Fintype.card I = 8)
    (hcases : ∀ j : Fin 5,
      (∃ C : Submodule K (Fin 3 → K), ∃ H : ThreeRayCover μ Finset.univ C,
        ∀ a, b j ∈ H.activeOutput F a) ∨
      (∃ i ∈ separatedIndices (K := K) (fun i ↦ quadraticVeronese (μ i)),
        b j ∈ Submodule.span K {F (Pi.single i 1)})) : False := by
  classical
  let sep := separatedIndices (K := K) (fun i ↦ quadraticVeronese (μ i))
  let Good (j : Fin 5) := ∃ C : Submodule K (Fin 3 → K),
    ∃ H : ThreeRayCover μ Finset.univ C, ∀ a, b j ∈ H.activeOutput F a
  have hsep : sep.card ≤ 3 := quadraticSeparatedIndices_card_le_three μ hp hcard.ge
  have hone : ∃ j, Good j := by
    by_contra hn
    have hbad (j : Fin 5) : ∃ i ∈ sep, b j ∈ Submodule.span K {F (Pi.single i 1)} := by
      exact (hcases j).resolve_left (fun h ↦ hn ⟨j, h⟩)
    let M : Submodule K L := Submodule.span K
      ((fun i ↦ F (Pi.single i 1)) '' (sep : Set I))
    have htop : M = ⊤ := by
      apply top_le_iff.mp
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      obtain ⟨i, hi, hj⟩ := hbad j
      have hmem : F (Pi.single i 1) ∈
          (fun i ↦ F (Pi.single i 1)) '' (sep : Set I) := ⟨i, hi, rfl⟩
      exact (Submodule.span_mono (Set.singleton_subset_iff.mpr hmem)) hj
    have hdimM : finrank K M ≤ sep.card := by
      have hh : finrank K M ≤
          ((fun i ↦ F (Pi.single i 1)) '' (sep : Set I)).ncard := by
        simpa only [M, Set.toFinset_card, Set.fintypeCard_eq_ncard] using
          (finrank_span_le_card (R := K) ((fun i ↦ F (Pi.single i 1)) '' (sep : Set I)))
      have hh' := hh.trans (Set.ncard_image_le (f := fun i ↦ F (Pi.single i 1))
        (s := (sep : Set I)))
      simpa only [Set.ncard_coe_finset] using hh'
    have hdim : finrank K L = 5 := by simpa using Module.finrank_eq_card_basis b
    rw [htop, finrank_top] at hdimM
    omega
  obtain ⟨j, C₀, H₀, _⟩ := hone
  have hnsep (i : I) : i ∉ sep :=
    H₀.not_quadratic_separated hp (by simpa using hcard.ge) i
  have hgood (j : Fin 5) : Good j := by
    rcases hcases j with h | ⟨i, hi, _⟩
    · exact h
    · exact False.elim (hnsep i hi)
  choose C H hout using hgood
  have hCin : Function.Injective C := by
    intro j k hCeq
    by_contra hjk
    have hpair : Function.Injective (![j, k] : Fin 2 → Fin 5) := by
      intro a c hac
      fin_cases a <;> fin_cases c
      · rfl
      · exact False.elim (hjk hac)
      · exact False.elim (hjk hac.symm)
      · rfl
    have hli : LinearIndependent K ![b j, b k] := by
      convert b.linearIndependent.comp (![j, k]) hpair using 1
      funext a
      fin_cases a <;> rfl
    exact (H j).center_ne_of_linearIndependent_outputs (H k)
      (by simp) F hker (b j) (b k) hli (hout j) (hout k) hCeq
  exact not_five_three_ray_covers_of_card_eight μ hp (by simp) Finset.univ
    (by simpa using hcard) C hCin H

end MMRank
