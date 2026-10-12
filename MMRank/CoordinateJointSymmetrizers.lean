module

public import MMRank.JointSymmetrizers
public import MMRank.RestrictedInputs
public import Mathlib.LinearAlgebra.Basis.Bilinear

@[expose] public section

/-! # Координатные блоки совместного симметризатора

Правое действие M на строках даёт условие симметрии именно M T,
а не T M. Размеры произвольны; базис параметрического пространства не нужен.
-/

namespace MMRank
open Matrix Module
variable {R P S Q Z : Type*} [CommRing R]
  [Fintype P] [Fintype S]
  [DecidableEq P] [DecidableEq S]
  [AddCommGroup Z] [Module R Z]

/-- Блок с параметром z и выходной координатой q: T(s,p)=B(z,e_p)(e_s)(q). -/
def jointSymmetrizerBlocks
    (B : Z →ₗ[R] (P → R) →ₗ[R] (S → R) →ₗ[R] (Q → R)) :
    Z × Q → Matrix S P R :=
  fun zq s p ↦ B zq.1 (Pi.single p 1) (Pi.single s 1) zq.2

omit [Fintype S] in
/-- Блок действует на столбец параметров; результат — значения физического отображения
на базисных строках. -/
theorem jointSymmetrizerBlocks_mulVec_apply
    (B : Z →ₗ[R] (P → R) →ₗ[R] (S → R) →ₗ[R] (Q → R))
    (z : Z) (q : Q) (u : P → R) (s : S) :
    (jointSymmetrizerBlocks B (z, q) *ᵥ u) s = B z u (Pi.single s 1) q := by
  rw [LinearMap.pi_apply_eq_sum_univ (B z)]
  simp only [mulVec, dotProduct, jointSymmetrizerBlocks, Finset.sum_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  have hp : (Pi.single p (1 : R) : P → R) = (fun j : P ↦ if p = j then (1 : R) else 0) := by
    ext j; simp [Pi.single_apply, eq_comm]
  rw [hp, mul_comm]

private theorem block_product_apply
    (B : Z →ₗ[R] (P → R) →ₗ[R] (S → R) →ₗ[R] (Q → R))
    (M : Matrix P S R) (z : Z) (q : Q) (p r : P) :
    (M * jointSymmetrizerBlocks B (z, q)) p r =
      B z (Pi.single r 1) (rowLinearEquiv M (Pi.single p 1)) q := by
  rw [rowLinearEquiv_apply, vecMulLinear_apply, single_one_vecMul]
  rw [LinearMap.pi_apply_eq_sum_univ (B z (Pi.single r 1))]
  simp only [Matrix.mul_apply, jointSymmetrizerBlocks, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (Pi.single i (1 : R) : S → R) = (fun j : S ↦ if i = j then (1 : R) else 0) := by
    ext j; simp [Pi.single_apply, eq_comm]
  rw [hi]
  rfl

theorem mem_jointSymmetrizer_iff_blocks
    (B : Z →ₗ[R] (P → R) →ₗ[R] (S → R) →ₗ[R] (Q → R))
    (M : Matrix P S R) :
    rowLinearEquiv M ∈ jointSymmetrizer B ↔
      M ∈ matrixJointSymmetrizer (jointSymmetrizerBlocks B) := by
  constructor
  · intro h ⟨z, q⟩
    apply IsSymm.ext
    intro p r
    simp only [block_product_apply]
    exact congrFun (h z (Pi.single p 1) (Pi.single r 1)) q
  · intro h z u v
    let C := (B z).compl₂ (rowLinearEquiv M)
    have he : C = C.flip := by
      apply LinearMap.ext_basis (Pi.basisFun R P) (Pi.basisFun R P)
      intro p r
      ext q
      change B z ((Pi.basisFun R P) p) (rowLinearEquiv M ((Pi.basisFun R P) r)) q =
        B z ((Pi.basisFun R P) r) (rowLinearEquiv M ((Pi.basisFun R P) p)) q
      simpa only [Pi.basisFun_apply, ← block_product_apply] using (h (z, q)).apply p r
    exact DFunLike.congr_fun (DFunLike.congr_fun he u) v

theorem jointSymmetrizer_eq_map_blocks
    (B : Z →ₗ[R] (P → R) →ₗ[R] (S → R) →ₗ[R] (Q → R)) :
    jointSymmetrizer B = (matrixJointSymmetrizer (jointSymmetrizerBlocks B)).map
      rowLinearEquiv.toLinearMap := by
  ext M
  constructor
  · intro hM
    refine ⟨rowLinearEquiv.symm M, ?_, rowLinearEquiv.apply_symm_apply M⟩
    apply (mem_jointSymmetrizer_iff_blocks B _).mp
    simpa using hM
  · rintro ⟨N, hN, rfl⟩
    exact (mem_jointSymmetrizer_iff_blocks B N).mpr hN

variable {K : Type*} [Field K] [Module K Z]

theorem finrank_jointSymmetrizer_eq_blocks
    (B : Z →ₗ[K] (P → K) →ₗ[K] (S → K) →ₗ[K] (Q → K)) :
    finrank K (jointSymmetrizer B) =
      finrank K (matrixJointSymmetrizer (jointSymmetrizerBlocks B)) := by
  rw [jointSymmetrizer_eq_map_blocks, LinearEquiv.finrank_map_eq]

end MMRank
