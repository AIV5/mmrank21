import MMRank.JointSymmetrizerPairCapacity
import MMRank.ProportionalBlockFactor
import MMRank.JointSymmetrizerDomain
import MMRank.JointSymmetrizerCodomain
import Mathlib.LinearAlgebra.Matrix.Dual

/-! # Факторизация из пяти совместных симметризаторов

Парная вместимость заменяет классификацию
сингулярных пространств и большие пространства симметричных матриц. Все поля.
-/

namespace MMRank
open Matrix Module
variable {K Z Q : Type*} [Field K] [AddCommGroup Z] [Module K Z]

/-- При пяти симметризаторах два блока с нулевым общим ядром пропорциональны. -/
theorem exists_smul_of_five_jointSymmetrizers
    (A B : Matrix (Fin 3) (Fin 3) K) (hA0 : A ≠ 0)
    (hk : ∀ u, A *ᵥ u = 0 → B *ᵥ u = 0 → u = 0)
    (H : Submodule K (Matrix (Fin 3) (Fin 3) K)) (hH : 5 ≤ finrank K H)
    (hA : ∀ M ∈ H, (M * A).IsSymm) (hB : ∀ M ∈ H, (M * B).IsSymm) :
    ∃ a : K, B = a • A := by
  by_contra! hn
  have hi : LinearIndependent K ![A, B] := (LinearIndependent.pair_iff' hA0).mpr (fun a ha ↦ hn a ha.symm)
  have hc := finrank_add_five_le_of_two_jointSymmetrizers A B hk
    (LinearIndependent.pair_iff.mp hi) H hA hB
  simp only [Fintype.card_fin] at hc
  omega

variable [Fintype Q]

/-- Одно инъективное сечение с выходом размерности≤2 выделяет обратимый блок.
Парная лемма затем охватывает блоки всех остальных сечений. -/
theorem exists_unit_blocks_of_five_jointSymmetrizers
    (B : Z →ₗ[K] (Fin 3 → K) →ₗ[K] (Fin 3 → K) →ₗ[K] (Q → K))
    (hQ : Fintype.card Q < 3) (hH : 5 ≤ finrank K (jointSymmetrizer B))
    (z : Z) (hz : Function.Injective (B z)) :
    ∃ U : (Matrix (Fin 3) (Fin 3) K)ˣ,
      ∀ zq, ∃ a : K, jointSymmetrizerBlocks B zq = a • (↑U : Matrix (Fin 3) (Fin 3) K) := by
  classical
  let T := jointSymmetrizerBlocks B
  let H := matrixJointSymmetrizer T
  have hd : 5 ≤ finrank K H := by rwa [finrank_jointSymmetrizer_eq_blocks] at hH
  have he (u : Fin 3 → K) (hu : ∀ q, T (z, q) *ᵥ u = 0) : u = 0 := by
    apply hz
    apply (Pi.basisFun K (Fin 3)).ext
    intro s
    ext q
    have hh := congrFun (hu q) s
    simpa only [T, jointSymmetrizerBlocks_mulVec_apply, Pi.basisFun_apply, map_zero,
      LinearMap.zero_apply, Pi.zero_apply] using hh
  obtain ⟨q₀, hT⟩ : ∃ q₀, T (z, q₀) ≠ 0 := by
    by_contra! hh
    have hu := he (Pi.single 0 1) (by intro q; rw [hh q]; exact zero_mulVec _)
    have h := congrFun hu 0
    simp at h
  have hprop (q : Q) : ∃ a : K, T (z, q) = a • T (z, q₀) := by
    by_cases hq : q = q₀
    · subst q; exact ⟨1, (one_smul K _).symm⟩
    have hcover (r : Q) : r = q₀ ∨ r = q := by
      by_contra! hr
      have hc : ({q₀, q, r} : Finset Q).card = 3 := by
        simp [Ne.symm hq, Ne.symm hr.1, Ne.symm hr.2]
      have hl := Finset.card_le_card (Finset.subset_univ ({q₀, q, r} : Finset Q))
      rw [hc, Finset.card_univ] at hl
      omega
    apply exists_smul_of_five_jointSymmetrizers _ _ hT ?_ H hd
      (fun M hM ↦ hM (z, q₀)) (fun M hM ↦ hM (z, q))
    intro u h0 h1
    apply he u
    intro r
    rcases hcover r with rfl | rfl <;> assumption
  have hi : Function.Injective (T (z, q₀)).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    change T (z, q₀) *ᵥ u = 0 at hu
    apply he u
    intro q
    obtain ⟨a, ha⟩ := hprop q
    rw [ha, smul_mulVec, hu, smul_zero]
  have hu : IsUnit (T (z, q₀)) := Matrix.mulVec_injective_iff_isUnit.mp hi
  refine ⟨hu.unit, ?_⟩
  intro zq
  rw [hu.unit_spec]
  apply exists_smul_of_five_jointSymmetrizers _ _ hT ?_ H hd
    (fun M hM ↦ hM (z, q₀)) (fun M hM ↦ hM zq)
  intro u h0 _
  exact hi (by simpa using h0)

/-- Большой совместный симметризатор и NZ дают оба фактора без классификации. -/
theorem exists_injective_factor_of_five_jointSymmetrizers [Nontrivial Z]
    (B : Z →ₗ[K] (Fin 3 → K) →ₗ[K] (Fin 3 → K) →ₗ[K] (Q → K))
    (hQ : Fintype.card Q < 3) (hH : 5 ≤ finrank K (jointSymmetrizer B))
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0) :
    ∃ U : (Matrix (Fin 3) (Fin 3) K)ˣ, ∃ f : Z →ₗ[K] (Q → K),
      Function.Injective f ∧ ∀ z u s,
        B z u s = (s ⬝ᵥ ((↑U : Matrix (Fin 3) (Fin 3) K) *ᵥ u)) • f z := by
  obtain ⟨z, hz⟩ := exists_ne (0 : Z)
  have hi : Function.Injective (B z) := by
    intro u v h
    apply sub_eq_zero.mp
    exact (hnz z (u - v) (by rw [map_sub, h, sub_self])).resolve_left hz
  obtain ⟨U, hU⟩ := exists_unit_blocks_of_five_jointSymmetrizers B hQ hH z hi
  obtain ⟨f, hf, he⟩ := exists_injective_linear_factor_of_proportional_matrix_blocks B U U.ne_zero hU hnz
  exact ⟨U, f, hf, he⟩

variable {U S W : Type*}
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup W] [Module K W]

/-- Координатно свободная факторизация, пригодная для физического второго кондуктора. -/
theorem exists_abstract_factor_of_five_jointSymmetrizers [Nontrivial Z]
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] W)
    (hU : finrank K U = 3) (hS : finrank K S = 3)
    (F : Submodule K W) [FiniteDimensional K F]
    (hF : finrank K F < 3) (hB : ∀ z u s, B z u s ∈ F)
    (hH : 5 ≤ finrank K (jointSymmetrizer B))
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0) :
    ∃ L : U ≃ₗ[K] Dual K S, ∃ f : Z →ₗ[K] F,
      Function.Injective f ∧ ∀ z u s, B z u s = (L u s) • (f z).val := by
  let a := (Module.finBasisOfFinrankEq K U hU).equivFun
  let b := (Module.finBasisOfFinrankEq K S hS).equivFun
  let e := (Module.finBasis K F).equivFun
  let C := domainCoordinateFamily B a.symm b.symm
  have hC : ∀ z u s, C z u s ∈ F := fun z u s ↦ hB z (a.symm u) (b.symm s)
  let D := codomainCoordinateFamily C F hC e
  have hc : 5 ≤ finrank K (jointSymmetrizer D) := by
    dsimp only [D]
    rw [jointSymmetrizer_codomainCoordinateFamily]
    dsimp only [C]
    rw [jointSymmetrizer_domainCoordinateFamily]
    simpa only [LinearEquiv.symm_symm, LinearEquiv.finrank_map_eq] using hH
  obtain ⟨T, f, hi, hf⟩ := exists_injective_factor_of_five_jointSymmetrizers D
    (by simpa using hF) hc
    (codomainCoordinateFamily_nz C F hC e (domainCoordinateFamily_nz B a.symm b.symm hnz))
  let v : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
    LinearEquiv.ofBijective (↑T : Matrix (Fin 3) (Fin 3) K).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr T.isUnit,
        Matrix.mulVec_surjective_iff_isUnit.mpr T.isUnit⟩
  refine ⟨a.trans ((v.trans (dotProductEquiv K (Fin 3))).trans b.dualMap),
    e.symm.toLinearMap.comp f, e.symm.injective.comp hi, ?_⟩
  intro z u s
  have hh := codomainCoordinateFamily_recover C F hC e z (a u) (b s)
  rw [hf] at hh
  change B z u s = (((↑T : Matrix (Fin 3) (Fin 3) K) *ᵥ a u) ⬝ᵥ b s) • (e.symm (f z)).val
  simpa only [C, domainCoordinateFamily_apply, LinearEquiv.symm_apply_apply,
    dotProduct_comm, map_smul, Submodule.coe_smul] using hh.symm

/-- При dimZ=dimF оба фактора обратимы. -/
theorem exists_abstract_equiv_factors_of_five_jointSymmetrizers [Nontrivial Z]
    [FiniteDimensional K Z]
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] W)
    (hU : finrank K U = 3) (hS : finrank K S = 3)
    (F : Submodule K W) [FiniteDimensional K F]
    (hF : finrank K F < 3) (hd : finrank K Z = finrank K F)
    (hB : ∀ z u s, B z u s ∈ F)
    (hH : 5 ≤ finrank K (jointSymmetrizer B))
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0) :
    ∃ L : U ≃ₗ[K] Dual K S, ∃ e : Z ≃ₗ[K] F,
      ∀ z u s, B z u s = (L u s) • (e z).val := by
  obtain ⟨L, f, hi, hf⟩ := exists_abstract_factor_of_five_jointSymmetrizers B hU hS F hF hB hH hnz
  exact ⟨L, LinearEquiv.ofBijective f
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩, hf⟩

end MMRank
