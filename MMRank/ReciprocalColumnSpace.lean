module

public import MMRank.SupportedTestSpace

@[expose] public section

namespace MMRank
open Matrix Module
variable {K P S : Type*} [Field K] [Fintype P] [Fintype S]

/-- Совместная колонковая оболочка пространства матриц. -/
def matrixColumnSpan (T : Submodule K (Matrix P S K)) : Submodule K (P → K) :=
  ⨆ C : T, C.val.transpose.vecMulLinear.range

omit [Fintype P] in
theorem mem_matrixColumnSpan (T : Submodule K (Matrix P S K)) (C : T) (s : S) :
    C.val.transpose s ∈ matrixColumnSpan T := by
  apply (le_iSup (fun D : T ↦ D.val.transpose.vecMulLinear.range) C)
  rw [range_vecMulLinear]
  exact Submodule.subset_span (Set.mem_range_self s)

omit [Fintype S] in
/-- Колонки транспонированного пространства — совместный правый образ
исходных матриц, без выбора базиса самого пространства. -/
theorem matrixColumnSpan_transpose (T : Submodule K (Matrix P S K)) :
    matrixColumnSpan (T.map (transposeLinearEquiv P S K K).toLinearMap) =
      ⨆ C : T, C.val.vecMulLinear.range := by
  let e := Submodule.equivMapOfInjective (transposeLinearEquiv P S K K).toLinearMap
    (transposeLinearEquiv P S K K).injective T
  simpa only [matrixColumnSpan, e, LinearEquiv.coe_toEquiv,
    Submodule.coe_equivMapOfInjective_apply, LinearEquiv.coe_coe,
    transposeLinearEquiv_apply, transposeAddEquiv, transpose_transpose] using
    (e.toEquiv.iSup_comp (g := fun C ↦ C.val.transpose.vecMulLinear.range)).symm

/-- Взаимность: общее левое ядро значений семейства совпадает с его
параметрическим ядром. Никаких ограничений на ранги не требуется. -/
theorem reciprocal_columnSpan_orthogonal
    (C : (P → K) →ₗ[K] Matrix P S K)
    (hsym : ∀ x y, x ᵥ* C y = y ᵥ* C x) :
    coordinateOrthogonal (matrixColumnSpan C.range) = C.ker := by
  classical
  ext x
  simp only [coordinateOrthogonal, matrixColumnSpan, Submodule.orthogonalBilin_iSup,
    Submodule.mem_iInf, range_vecMulLinear, Submodule.mem_orthogonalBilin_span,
    Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h
    change C x = 0
    ext p s
    have hh := h ⟨C (Pi.single p 1), ⟨Pi.single p 1, rfl⟩⟩ s
    have hh' : (x ᵥ* C (Pi.single p 1)) s = 0 := by
      simpa [vecMul, Matrix.col, Matrix.transpose, dotProduct_comm] using hh
    rw [hsym, single_vecMul] at hh'
    simpa using hh'
  · intro hx D s
    obtain ⟨y, hy⟩ := D.property
    change C x = 0 at hx
    rw [← hy]
    simpa [hx, vecMul, Matrix.col, Matrix.transpose, dotProduct_comm] using congrFun (hsym x y) s

/-- Размер совместной колонковой оболочки симметричного семейства равен
рангу самого семейства, не рангу отдельного значения. -/
theorem finrank_reciprocal_columnSpan
    (C : (P → K) →ₗ[K] Matrix P S K)
    (hsym : ∀ x y, x ᵥ* C y = y ᵥ* C x) :
    finrank K (matrixColumnSpan C.range) = finrank K C.range := by
  have ho := finrank_coordinateOrthogonal (matrixColumnSpan C.range)
  rw [reciprocal_columnSpan_orthogonal C hsym] at ho
  have hr := C.finrank_range_add_finrank_ker
  have hb := Submodule.finrank_le (matrixColumnSpan C.range)
  simp only [Module.finrank_fintype_fun_eq_card] at hr hb
  omega

omit [Fintype S] in
theorem coordinateOrthogonal_involutive (F : Submodule K (P → K)) :
    coordinateOrthogonal (coordinateOrthogonal F) = F := by
  apply LinearMap.BilinForm.orthogonal_orthogonal (coordinatePairing_nondegenerate (K := K))
  intro x y h
  change y ⬝ᵥ x = 0
  change x ⬝ᵥ y = 0 at h
  rwa [dotProduct_comm]

theorem reciprocal_columnSpan_eq_orthogonal_ker
    (C : (P → K) →ₗ[K] Matrix P S K)
    (hsym : ∀ x y, x ᵥ* C y = y ᵥ* C x) :
    matrixColumnSpan C.range = coordinateOrthogonal C.ker := by
  rw [← reciprocal_columnSpan_orthogonal C hsym, coordinateOrthogonal_involutive]

end MMRank
