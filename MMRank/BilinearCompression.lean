module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # Сжатие билинейной формулы по оболочке простых пар -/

namespace MMRank
open Module
variable {K U V W I : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype I]

/-- Если все срезы билинейного отображения лежат в оболочке конечного
семейства простых пар, формула сжимается до размерности этой оболочки.
Первые формы и выходы выбираются из исходных пар без изменения;
меняются только вторые формы. Конечномерность U,V,W не нужна. -/
theorem exists_bilinear_compression (a : I → U →ₗ[K] K) (w : I → W)
    (f : V →ₗ[K] U →ₗ[K] W)
    (hf : ∀ v, f v ∈ Submodule.span K (Set.range (fun i ↦ (a i).smulRight (w i)))) :
    ∃ (n : ℕ) (idx : Fin n → I) (b : Fin n → V →ₗ[K] K),
      Function.Injective idx ∧
      n = finrank K (Submodule.span K (Set.range (fun i ↦ (a i).smulRight (w i)))) ∧
      ∀ u v, f v u = ∑ j, (a (idx j) u * b j v) • w (idx j) := by
  classical
  let t : I → U →ₗ[K] W := fun i ↦ (a i).smulRight (w i)
  obtain ⟨J, idx, hi, hs, hli⟩ := exists_linearIndependent' K t
  let : Finite J := Finite.of_injective idx hi
  let : Fintype J := Fintype.ofFinite J
  let B := Basis.span hli
  let g := f.codRestrict (Submodule.span K (Set.range (t ∘ idx)))
    (fun v ↦ by rw [hs]; exact hf v)
  let b : J → V →ₗ[K] K := fun j ↦ (B.coord j).comp g
  have hrec (u : U) (v : V) : f v u = ∑ j, (a (idx j) u * b j v) • w (idx j) := by
    have hh := congrArg (fun z : Submodule.span K (Set.range (t ∘ idx)) ↦ z.val u)
      (B.sum_repr (g v))
    simpa [B, b, g, t, LinearMap.sum_apply, smul_smul, mul_comm] using hh.symm
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, idx ∘ e, b ∘ e, hi.comp e.injective, ?_, ?_⟩
  · rw [← hs]
    exact (finrank_span_eq_card hli).symm
  · intro u v
    exact (hrec u v).trans (e.sum_comp (fun j ↦ (a (idx j) u * b j v) • w (idx j))).symm

end MMRank
