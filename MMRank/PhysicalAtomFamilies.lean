module

public import MMRank.PhysicalAtomIntersections

@[expose] public section

/-! # Семейства атомов и два общих соседа -/
namespace MMRank.ExactAlgorithm.PhysicalAtom
open Matrix
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  {alg : ExactAlgorithm K P Q S I}

/-- Общий индекс двух атомов одного типа делает их тесты пропорциональными.
Это следует из двух диагональных тождеств, без полноты физических классов. -/
theorem test_smul_of_common_index (a b : PhysicalAtom alg) {i : I}
    (ha : i ∈ a.support) (hb : i ∈ b.support) :
    ∃ k : K, k ≠ 0 ∧ b.test = k • a.test := by
  have hA := a.weighted_product ⟨i, ha⟩ ⟨i, ha⟩
  have hB := b.weighted_product ⟨i, hb⟩ ⟨i, hb⟩
  simp only [ite_true, one_smul] at hA hB
  refine ⟨alg.toCoefficients.gamma b.test i / alg.toCoefficients.gamma a.test i,
    div_ne_zero hb ha, ?_⟩
  calc
    b.test = alg.toCoefficients.gamma b.test i • (alg.U i * alg.V i) := hB.symm
    _ = (alg.toCoefficients.gamma b.test i / alg.toCoefficients.gamma a.test i) •
        (alg.toCoefficients.gamma a.test i • (alg.U i * alg.V i)) := by
      rw [smul_smul, div_mul_cancel₀ _ ha]
    _ = _ := congrArg (fun X ↦
      (alg.toCoefficients.gamma b.test i / alg.toCoefficients.gamma a.test i) • X) hA

/-- Разные носители атомов одного типа не пересекаются в любых размерах. -/
theorem support_eq_or_disjoint (a b : PhysicalAtom alg) :
    a.support = b.support ∨ Disjoint a.support b.support := by
  by_cases hd : Disjoint a.support b.support
  · exact Or.inr hd
  · left
    obtain ⟨i, ha, hb⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨k, hk, he⟩ := a.test_smul_of_common_index b ha hb
    ext j
    change alg.toCoefficients.gamma a.test j ≠ 0 ↔ alg.toCoefficients.gamma b.test j ≠ 0
    rw [he, map_smul]
    change _ ↔ k * alg.toCoefficients.gamma a.test j ≠ 0
    exact ⟨fun hj ↦ mul_ne_zero hk hj, fun hj ↦ (mul_ne_zero_iff.mp hj).2⟩

/-- Инъективно выбранные носители атомов попарно не пересекаются.
Число атомов и физические размеры произвольны. -/
theorem pairwise_disjoint_support {J : Type*} (a : J → PhysicalAtom alg)
    (ha : Function.Injective (fun j ↦ (a j).support)) :
    Pairwise (fun j k ↦ Disjoint (a j).support (a k).support) :=
  fun _ _ h ↦ (support_eq_or_disjoint _ _).resolve_left (fun he ↦ h (ha he))

end MMRank.ExactAlgorithm.PhysicalAtom
