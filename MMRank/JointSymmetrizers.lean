import MMRank.CommonLineRigidity
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Совместные симметризаторы и перенос взаимности

Общие определения над коммутативным кольцом; порядок композиций
соответствует правому действию физических отображений.
-/

namespace MMRank
variable {R U S W Z : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup S] [Module R S]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]

/-- M симметризует B, если B(z,u)(M v)=B(z,v)(M u). -/
def jointSymmetrizer (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W) :
    Submodule R (U →ₗ[R] S) where
  carrier := {M | ∀ z u v, B z u (M v) = B z v (M u)}
  zero_mem' := by simp
  add_mem' := by
    intro M N hM hN z u v
    simp only [LinearMap.add_apply, map_add]
    rw [hM z u v, hN z u v]
  smul_mem' := by
    intro a M hM z u v
    simp only [LinearMap.smul_apply, map_smul]
    rw [hM z u v]

/-- Взаимность C и совместимость двух семейств помещают каждое C(w)
в пространство совместных симметризаторов; конечномерность не нужна. -/
theorem reciprocal_family_mem_jointSymmetrizer
    (B : Z →ₗ[R] U →ₗ[R] S →ₗ[R] W) (C : U →ₗ[R] U →ₗ[R] S)
    (hC : ∀ u v, C u v = C v u)
    (hBC : ∀ z u v, (B z u).comp (C v) = (B z v).comp (C u))
    (w : U) : C w ∈ jointSymmetrizer B := by
  intro z u v
  calc
    B z u (C w v) = B z u (C v w) := by rw [hC w v]
    _ = B z v (C u w) := DFunLike.congr_fun (hBC z u v) w
    _ = B z v (C w u) := by rw [hC u w]

variable {m n ι : Type*} [Fintype n]

/-- Матричная форма: все произведения M Tᵢ симметричны.
Число блоков произвольно, сами блоки могут быть прямоугольными. -/
def matrixJointSymmetrizer (T : ι → Matrix n m R) : Submodule R (Matrix m n R) where
  carrier := {M | ∀ i, (M * T i).IsSymm}
  zero_mem' := by intro i; simp
  add_mem' := by intro M N hM hN i; rw [Matrix.add_mul]; exact (hM i).add (hN i)
  smul_mem' := by intro a M hM i; rw [Matrix.smul_mul]; exact (hM i).smul a

end MMRank
