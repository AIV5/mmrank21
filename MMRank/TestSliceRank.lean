import MMRank.ReciprocalColumnSpace
import MMRank.RestrictedRankBudget

/-! # Полная свёртка пространства тестов и её ранг -/

namespace MMRank
open Matrix Module
variable {K P Q S : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S]

/-- A сопоставляется сразу всем произведениям AC, C∈T. -/
def leftTestSlices (T : Submodule K (Matrix P S K)) :
    Matrix Q P K →ₗ[K] (T →ₗ[K] Matrix Q S K) where
  toFun A :=
    { toFun := fun C ↦ A * C.val
      map_add' := by intros; exact Matrix.mul_add _ _ _
      map_smul' := by intros; exact Matrix.mul_smul _ _ _ }
  map_add' := by intros; ext C q s; exact congrFun (congrFun (Matrix.add_mul _ _ _) q) s
  map_smul' := by intros; ext C q s; exact congrFun (congrFun (Matrix.smul_mul _ _ _) q) s

/-- Ядро полной свёртки состоит из матриц со строками, ортогональными
всей совместной колонковой оболочке тестов. -/
theorem ker_leftTestSlices (T : Submodule K (Matrix P S K)) :
    (leftTestSlices (Q := Q) T).ker = matricesInto (coordinateOrthogonal (matrixColumnSpan T)) := by
  classical
  ext A
  rw [mem_matricesInto, range_vecMulLinear, Submodule.span_le]
  constructor
  · intro h
    rintro _ ⟨q, rfl⟩
    have hz (C : T) : A * C.val = 0 := DFunLike.congr_fun h C
    have hle : matrixColumnSpan T ≤ (dotProductBilin K K (A q)).ker := by
      apply iSup_le
      intro C
      rw [range_vecMulLinear, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      exact congrFun (congrFun (hz C) q) s
    intro v hv
    have hh := hle hv
    simpa only [LinearMap.mem_ker, dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk,
      dotProduct_comm, Matrix.row] using hh
  · intro h
    change leftTestSlices T A = 0
    ext C q s
    have hh := h ⟨q, rfl⟩ _ (mem_matrixColumnSpan T C s)
    change A q ⬝ᵥ C.val.transpose s = 0
    simpa only [dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_comm,
      Matrix.row] using hh

/-- Ранг полной свёртки равен q·dim F для совместной колонковой
оболочки F; размерности T и отдельных тестов не ограничиваются. -/
theorem finrank_leftTestSlices (T : Submodule K (Matrix P S K)) :
    finrank K (leftTestSlices (Q := Q) T).range =
      Fintype.card Q * finrank K (matrixColumnSpan T) := by
  have hr := (leftTestSlices (Q := Q) T).finrank_range_add_finrank_ker
  rw [ker_leftTestSlices, finrank_matricesInto, finrank_coordinateOrthogonal] at hr
  have hmat : finrank K (Matrix Q P K) = Fintype.card Q * Fintype.card P := by
    simp [Module.finrank_matrix]
  rw [hmat] at hr
  have hf := Submodule.finrank_le (matrixColumnSpan T)
  rw [Module.finrank_fintype_fun_eq_card] at hf
  have he : Fintype.card P = finrank K (matrixColumnSpan T) +
      (Fintype.card P - finrank K (matrixColumnSpan T)) := by omega
  nlinarith [Nat.mul_add (Fintype.card Q) (finrank K (matrixColumnSpan T))
    (Fintype.card P - finrank K (matrixColumnSpan T))]

end MMRank
