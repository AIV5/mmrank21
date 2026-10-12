import MMRank.Algorithm
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Перенумерация физических координат точного алгоритма -/
namespace MMRank
open Matrix
variable {K P Q S P' Q' S' I : Type*} [CommSemiring K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype P'] [Fintype Q'] [Fintype S'] [Fintype I]

/-- Контрагредиентная перенумерация входа сохраняет следовую форму. -/
theorem trace_relabel_pair (U : Matrix P Q K) (A : Matrix Q' P' K)
    (eP : P ≃ P') (eQ : Q ≃ Q') :
    trace (U.submatrix eP.symm eQ.symm * A) = trace (U * A.submatrix eQ eP) := by
  have ht (M : Matrix P P K) : trace (M.submatrix eP.symm eP.symm) = trace M :=
    eP.symm.sum_comp (fun p ↦ M p p)
  rw [← ht (U * A.submatrix eQ eP), ← submatrix_mul_equiv _ _ _ eQ.symm]
  simp

/-- Физические координаты и индексы слагаемых независимы: здесь
перенумеровываются только P,Q,S, а I не меняется. -/
def ExactAlgorithm.relabel (alg : ExactAlgorithm K P Q S I)
    (eP : P ≃ P') (eQ : Q ≃ Q') (eS : S ≃ S') : ExactAlgorithm K P' Q' S' I where
  U i := (alg.U i).submatrix eP.symm eQ.symm
  V i := (alg.V i).submatrix eQ.symm eS.symm
  W i := (alg.W i).submatrix eS.symm eP.symm
  exact_formula := by
    intro A B
    change B * A = ∑ i, (trace ((alg.U i).submatrix eP.symm eQ.symm * A) *
      trace ((alg.V i).submatrix eQ.symm eS.symm * B)) • (alg.W i).submatrix eS.symm eP.symm
    simp only [trace_relabel_pair]
    have hh := congrArg (fun M : Matrix S P K ↦ M.submatrix eS.symm eP.symm)
      (alg.exact_formula (A.submatrix eQ eP) (B.submatrix eS eQ))
    rw [← submatrix_mul_equiv _ _ _ eQ.symm] at hh
    simp only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at hh
    ext s p
    simpa only [Coefficients.evaluate, submatrix_apply, Matrix.sum_apply, Finset.sum_apply,
      Matrix.smul_apply] using congrFun (congrFun hh s) p

end MMRank
