import MMRank.RestrictedCoefficients
import MMRank.AlgorithmGeneralPosition
import MMRank.LengthReduction
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Носители ограниченных следовых координат

Критерии не требуют точности алгоритма или бесконечности поля.
Полный носитель означает существование своего элемента для каждой координаты.
-/

namespace MMRank

open Matrix Module

variable {K P Q S ι : Type*} [Field K] [Fintype P] [Fintype Q] [Fintype S]

/-- Следовая форма U ненулевая на входах, зануляющих F, ровно когда im U ⊈ F. -/
theorem exists_trace_ne_zero_killing_iff (U : Matrix P Q K) (F : Submodule K (Q → K)) :
    (∃ A ∈ matricesKilling F, trace (U * A) ≠ 0) ↔ ¬ U.vecMulLinear.range ≤ F := by
  classical
  constructor
  · rintro ⟨A, hA, htrace⟩ hU
    apply htrace
    rw [mul_eq_zero_of_restricted F A U hA ((mem_matricesInto F U).mpr hU)]
    simp
  · contrapose!
    intro h
    rw [range_vecMulLinear, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    by_contra hp
    obtain ⟨φ, hφp, hφF⟩ := Submodule.exists_le_ker_of_notMem hp
    let v : Q → K := fun q ↦ φ (fun j ↦ if q = j then 1 else 0)
    have hv (x : Q → K) : x ⬝ᵥ v = φ x := by
      simpa [dotProduct, v] using (φ.pi_apply_eq_sum_univ x).symm
    let A : Matrix Q P K := vecMulVec v (Pi.single p 1)
    have hA : A ∈ matricesKilling F := by
      apply (mem_matricesKilling F A).mpr
      intro x hx
      change x ᵥ* A = 0
      rw [vecMul_vecMulVec, hv, hφF hx, zero_smul]
    have ht : trace (U * A) = φ (U p) := by
      simp only [A, mul_vecMulVec, trace_vecMulVec]
      simpa [dotProduct, mulVec, Pi.single_apply] using hv (U p)
    exact hφp (ht.symm.trans (h A hA))

omit [Field K] in
/-- Следовая форма V ненулевая на входах со значениями в F ровно когда V|F ≠ 0. -/
theorem exists_trace_ne_zero_into_iff [CommSemiring K]
    (V : Matrix Q S K) (F : Submodule K (Q → K)) :
    (∃ B ∈ matricesInto F, trace (V * B) ≠ 0) ↔ ¬ F ≤ V.vecMulLinear.ker := by
  classical
  constructor
  · rintro ⟨B, hB, ht⟩ hV
    apply ht
    rw [trace_mul_comm, mul_eq_zero_of_restricted F V B
      ((mem_matricesKilling F V).mpr hV) hB]
    simp
  · intro hV
    obtain ⟨x, hx, hxV⟩ := IsConcreteLE.not_le_iff_exists.mp hV
    have hn : x ᵥ* V ≠ 0 := hxV
    obtain ⟨s, hs⟩ : ∃ s, (x ᵥ* V) s ≠ 0 := Function.ne_iff.mp hn
    let B : Matrix S Q K := vecMulVec (Pi.single s 1) x
    refine ⟨B, ?_, ?_⟩
    · apply (mem_matricesInto F B).mpr
      rintro _ ⟨y, rfl⟩
      change y ᵥ* B ∈ F
      rw [vecMul_vecMulVec]
      exact F.smul_mem _ hx
    · rw [trace_mul_comm, vecMulVec_mul, trace_vecMulVec]
      simpa [dotProduct, Pi.single_apply] using hs

namespace Coefficients

omit [Fintype S] in
/-- Координатный носитель A_F характеризуется включением образа U_i в F. -/
theorem alphaOn_coord_nonzero_iff (d : Coefficients K P Q S ι)
    (F : Submodule K (Q → K)) (i : ι) :
    (∃ a ∈ d.alphaOn F, a i ≠ 0) ↔ ¬ (d.U i).vecMulLinear.range ≤ F := by
  rw [← exists_trace_ne_zero_killing_iff]
  constructor
  · rintro ⟨a, ⟨A, hA, rfl⟩, ha⟩
    exact ⟨A, hA, ha⟩
  · rintro ⟨A, hA, ha⟩
    exact ⟨d.alpha A, ⟨A, hA, rfl⟩, ha⟩

omit [Fintype P] [Field K] in
/-- Координатный носитель B_F характеризуется ненулевостью ограничения V_i|F. -/
theorem betaInto_coord_nonzero_iff [CommSemiring K] (d : Coefficients K P Q S ι)
    (F : Submodule K (Q → K)) (i : ι) :
    (∃ b ∈ d.betaInto F, b i ≠ 0) ↔ ¬ F ≤ (d.V i).vecMulLinear.ker := by
  rw [← exists_trace_ne_zero_into_iff]
  constructor
  · rintro ⟨b, ⟨B, hB, rfl⟩, hb⟩
    exact ⟨B, hB, hb⟩
  · rintro ⟨B, hB, hb⟩
    exact ⟨d.beta B, ⟨B, hB, rfl⟩, hb⟩

end Coefficients

omit [Fintype P] [Fintype Q] [Fintype S] in
/-- Полный носитель подпространства над бесконечным полем даёт один элемент без нулей. -/
theorem exists_mem_forall_ne_zero [Infinite K] [Finite ι] (M : Submodule K (ι → K))
    (hM : ∀ i, ∃ a ∈ M, a i ≠ 0) : ∃ a ∈ M, ∀ i, a i ≠ 0 :=
  Module.Dual.exists_forall_mem_ne_zero_of_forall_exists M (fun i ↦ LinearMap.proj i) hM

namespace ExactAlgorithm

variable [Fintype ι] [Infinite K]

end ExactAlgorithm

end MMRank
