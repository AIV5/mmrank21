import MMRank.ExteriorPairRelations
import MMRank.BilinearCompression
import MMRank.QuotientMatrixChart
import MMRank.TraceDuality

/-! # Реальная прямоугольная формула после сжатия внешних пар -/

namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped Classical
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Подстановка по F даёт точный алгоритм с размером среднего пространства
dim(Q/F) и длиной, равной размерности оболочки внешних простых пар.
Это построение алгоритма, не предположение об аддитивности ранга. -/
theorem exists_rectangular_compression (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I)
    (hG : ∀ i ∈ G, alg.U i ∈ matricesInto (S := P) F) :
    ∃ (n : ℕ), Nonempty (ExactAlgorithm K P (Fin (finrank K ((Q → K) ⧸ F))) S (Fin n)) ∧
      n = finrank K (alg.toCoefficients.externalPairSum F G).range := by
  classical
  let X := matricesKilling (P := P) F
  let a : ↥(Gᶜ) → X →ₗ[K] K := fun i ↦
    (LinearMap.proj i.val).comp (alg.toCoefficients.alpha.domRestrict X)
  let w : ↥(Gᶜ) → Matrix S P K := fun i ↦ alg.W i.val
  let f : Matrix S Q K →ₗ[K] X →ₗ[K] Matrix S P K :=
    (LinearMap.domRestrict' X).comp (mulLinearMap K)
  have hr : (alg.toCoefficients.externalPairSum F G).range =
      Submodule.span K (Set.range (fun i ↦ (a i).smulRight (w i))) := by
    exact Fintype.range_linearCombination K _
  obtain ⟨n, idx, b, _, hn, hform⟩ := exists_bilinear_compression a w f (fun B ↦ by
    rw [← hr]
    exact alg.slice_mem_externalPairSum_range F G hG B)
  obtain ⟨D, C, hCD, hD⟩ := exists_quotient_matrix_chart F
  have hv (j : Fin n) : ∃ V : Matrix (Fin (finrank K ((Q → K) ⧸ F))) S K,
      ∀ B : Matrix S (Fin (finrank K ((Q → K) ⧸ F))) K, b j (B * C) = trace (V * B) := by
    obtain ⟨V, hV, _⟩ := exists_unique_trace_representation ((b j).comp (mulRightLinearMap S K C))
    exact ⟨V, fun B ↦ (hV B).trans (trace_mul_comm B V)⟩
  choose V hV using hv
  refine ⟨n, ⟨{
    U := fun j ↦ alg.U (idx j) * D
    V := V
    W := fun j ↦ alg.W (idx j)
    exact_formula := ?_ }⟩, by rwa [hr]⟩
  intro A B
  have hA : D * A ∈ X := by
    apply (mem_matricesKilling F (D * A)).mpr
    intro x hx
    change x ᵥ* (D * A) = 0
    have hz : x ᵥ* D = 0 := hD hx
    rw [← vecMul_vecMul, hz, zero_vecMul]
  have hh := hform ⟨D * A, hA⟩ (B * C)
  change (B * C) * (D * A) = ∑ j,
    (trace (alg.U (idx j) * (D * A)) * b j (B * C)) • alg.W (idx j) at hh
  have hprod : (B * C) * (D * A) = B * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C D A, hCD, Matrix.one_mul]
  rw [hprod] at hh
  change B * A = ∑ j, (trace ((alg.U (idx j) * D) * A) * trace (V j * B)) • alg.W (idx j)
  simpa only [Matrix.mul_assoc, hV] using hh

end MMRank.ExactAlgorithm
