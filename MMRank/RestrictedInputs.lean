import MMRank.CoefficientMaps
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Входы, зануляющие F, и входы со значениями в F

Размерности устанавливаются до выбора общего положения и не требуют точного алгоритма.
Матричные соглашения сохраняют правое действие на строках.
-/

namespace MMRank

open Module

variable {K P Q S : Type*} [Fintype P] [Fintype Q] [Fintype S]

section Semiring

variable [CommSemiring K]

/-- K-линейный мост между матрицей и её правым действием на строках. -/
noncomputable def rowLinearEquiv : Matrix Q P K ≃ₗ[K] ((Q → K) →ₗ[K] (P → K)) := by
  classical
  exact (Matrix.transposeLinearEquiv Q P K K).trans Matrix.toLin'

omit [Fintype P] in
@[simp] theorem rowLinearEquiv_apply (A : Matrix Q P K) :
    rowLinearEquiv A = A.vecMulLinear := by
  ext x p
  simp [rowLinearEquiv, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]

/-- Линейное ограничение правого действия на F. -/
noncomputable def rowRestriction (F : Submodule K (Q → K)) :
    Matrix Q P K →ₗ[K] (F →ₗ[K] (P → K)) :=
  (LinearMap.domRestrict' F).comp rowLinearEquiv.toLinearMap

/-- Входы A, зануляющие F. -/
noncomputable def matricesKilling (F : Submodule K (Q → K)) :
    Submodule K (Matrix Q P K) := (rowRestriction F).ker

omit [Fintype P] in
@[simp] theorem mem_matricesKilling (F : Submodule K (Q → K)) (A : Matrix Q P K) :
    A ∈ matricesKilling F ↔ F ≤ A.vecMulLinear.ker := by
  change rowRestriction F A = 0 ↔ _
  simp only [rowRestriction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    rowLinearEquiv_apply]
  constructor
  · intro h x hx
    exact congrArg (fun f : F →ₗ[K] (P → K) ↦ f ⟨x, hx⟩) h
  · intro h
    ext x p
    exact congrFun (h x.property) p

/-- Вложение семейства строк из F в пространство матриц. -/
def rowsInclusion (F : Submodule K (Q → K)) : (S → F) →ₗ[K] Matrix S Q K where
  toFun B s := B s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Входы B со значениями в F. -/
def matricesInto (F : Submodule K (Q → K)) : Submodule K (Matrix S Q K) :=
  (rowsInclusion F).range

omit [Fintype Q] in
@[simp] theorem mem_matricesInto (F : Submodule K (Q → K)) (B : Matrix S Q K) :
    B ∈ matricesInto F ↔ B.vecMulLinear.range ≤ F := by
  rw [range_vecMulLinear, Submodule.span_le]
  constructor
  · rintro ⟨b, rfl⟩ _ ⟨s, rfl⟩
    exact (b s).property
  · intro h
    exact ⟨fun s ↦ ⟨B s, h ⟨s, rfl⟩⟩, rfl⟩

omit [Fintype P] in
/-- Если im B ≤ F ≤ ker A, то BA = 0; условие общего положения не нужно. -/
theorem mul_eq_zero_of_restricted (F : Submodule K (Q → K))
    (A : Matrix Q P K) (B : Matrix S Q K)
    (hA : A ∈ matricesKilling F) (hB : B ∈ matricesInto F) : B * A = 0 := by
  apply rowLinearEquiv.injective
  rw [rowLinearEquiv_apply, map_zero, rowLinear_mul]
  exact LinearMap.range_le_ker_iff.mp ((mem_matricesInto F B).mp hB |>.trans
    ((mem_matricesKilling F A).mp hA))

end Semiring

variable [Field K]

omit [Fintype P] in
/-- Ограничение на F сюръективно: линейное отображение продолжается на всё Q. -/
theorem rowRestriction_surjective (F : Submodule K (Q → K)) :
    Function.Surjective (rowRestriction (P := P) F) := by
  intro f
  obtain ⟨g, hg⟩ := f.exists_extend
  refine ⟨rowLinearEquiv.symm g, ?_⟩
  change LinearMap.domRestrict' F (rowLinearEquiv (rowLinearEquiv.symm g)) = f
  rw [LinearEquiv.apply_symm_apply]
  exact hg

/-- dim {A : FA = 0} = p(q − dim F), включая нулевые размеры. -/
theorem finrank_matricesKilling (F : Submodule K (Q → K)) :
    finrank K (matricesKilling (P := P) F) =
      Fintype.card P * (Fintype.card Q - finrank K F) := by
  have h := (rowRestriction (P := P) F).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (rowRestriction_surjective F), finrank_top,
    Module.finrank_linearMap, Module.finrank_pi, Module.finrank_matrix] at h
  change _ + finrank K (matricesKilling (P := P) F) = _ at h
  simp only [finrank_self, Nat.mul_one] at h
  rw [Nat.mul_sub_left_distrib, Nat.mul_comm (Fintype.card P),
    Nat.mul_comm (Fintype.card P)]
  omega

/-- dim {B : im B ≤ F} = s dim F. -/
theorem finrank_matricesInto (F : Submodule K (Q → K)) :
    finrank K (matricesInto (S := S) F) = Fintype.card S * finrank K F := by
  have hi : Function.Injective (rowsInclusion (S := S) F) := by
    intro B B' h
    funext s
    exact Subtype.ext (congrFun h s)
  rw [matricesInto, LinearMap.finrank_range_of_inj hi, Module.finrank_pi_fintype]
  simp

end MMRank
