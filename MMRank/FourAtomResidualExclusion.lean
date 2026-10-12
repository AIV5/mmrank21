module

public import MMRank.CriticalResidualExclusion
public import MMRank.CriticalThreeAnnihilator
public import MMRank.PhysicalAtomResidual
public import MMRank.PhysicalAtomDirections

@[expose] public section

/-! # Четыре физических атома исключаются одним остаточным бюджетом
Бесконечность нужна только для готового
переноса независимости внешних направлений; остаточный бюджет поленезависим.
-/
noncomputable section
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

/-- Четыре атома оставляют восемь простых срезов для пяти независимых тестов. -/
theorem four_physical_atoms_impossible_by_residual
    (alg : ExactAlgorithm K (Fin 3) (Fin 3) (Fin 3) I)
    (hl : Fintype.card I = 20) (hn : alg.toCoefficients.NonzeroTerms)
    (a : Fin 4 → PhysicalAtom alg)
    (ha : Function.Injective (fun j ↦ (a j).support)) : False := by
  classical
  obtain ⟨G, hc, hG, _⟩ := PhysicalAtom.union_rank_one a ha
  have hGc : G.card = 12 := by simpa using hc
  have hcount : Fintype.card {i // i ∉ G} = 8 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_coe, hGc, hl]
  let τ (j : Fin 4) : Matrix (Fin 3) (Fin 3) K →ₗ[K] K :=
    (traceLinearMap (Fin 3) K K).comp (mulRightLinearMap (Fin 3) K (a j).test)
  let R : Submodule K (Matrix (Fin 3) (Fin 3) K) := ⨅ j, (τ j).ker
  have hR (T) : T ∈ R ↔ ∀ j, trace (T * vecMulVec (a j).first (a j).last) = 0 := by
    simp only [R, Submodule.mem_iInf, LinearMap.mem_ker, τ, LinearMap.comp_apply,
      traceLinearMap_apply, mulRightLinearMap_apply]
    rfl
  have hdir (e : Fin 3 → Fin 4) (he : Function.Injective e) :
      LinearIndependent K (fun i ↦ (a (e i)).first) ∧
      LinearIndependent K (fun i ↦ (a (e i)).last) :=
    PhysicalAtom.three_directions_linearIndependent (fun i ↦ a (e i)) rfl rfl rfl
      hl.le hn (ha.comp he)
  obtain ⟨b, hb⟩ := CriticalThreeAnnihilator.exists_frame_annihilator_basis R
    (fun j ↦ (a j).first) (fun j ↦ (a j).last) hR
    (fun e he ↦ (hdir e he).1) (fun e he ↦ (hdir e he).2)
  have hw (i : {i // i ∉ G}) : alg.W i.val ∈ R := by
    apply (hR _).mpr
    intro j
    exact PhysicalAtom.residual_output_annihilates_testSpan a G hG i (a j).test
      (Submodule.subset_span (Set.mem_range_self j))
  let w (i : {i // i ∉ G}) : R := ⟨alg.W i.val, hw i⟩
  let A (j : Fin 5) (i : {i // i ∉ G}) := alg.V i.val * (b j).val * alg.U i.val
  apply not_eight_rank_one_reconstruction b w hcount A
  · intro j i
    exact ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)).trans (hb j).le
  · intro j X
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ i : {i // i ∉ G}, trace (X * A j i) • alg.W i.val) = trace X • (b j).val
    apply PhysicalAtom.residual_sandwich_trace_identity a G hG (b j).val
    intro k
    exact (trace_mul_comm _ _).trans ((hR _).mp (b j).property k)

end MMRank.ExactAlgorithm
