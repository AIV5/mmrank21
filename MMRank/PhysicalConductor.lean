import MMRank.ConductorRealization
import MMRank.RestrictedCoefficients
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Физическое представление кондуктора и взаимность

Подъём произведения α(A)d через γ даёт матрицу C_d(A).
Точность алгоритма делает соответствующее спаривание симметричным по A,A'.
-/

namespace MMRank

open Matrix Module
open scoped BigOperators

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

namespace ExactAlgorithm

variable [Nonempty Q]

/-- Матрица C_d(A), единственный прообраз α(A)d под γ. -/
noncomputable def conductorMatrix (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F)) :
    matricesKilling (P := P) F →ₗ[K] Matrix P S K :=
  ((conductorLift alg.toCoefficients.gamma alg.gamma_injective
    (alg.toCoefficients.alphaOn F)).flip d).comp
      ((alg.toCoefficients.alpha.comp (matricesKilling F).subtype).codRestrict
        (alg.toCoefficients.alphaOn F) fun A ↦ Submodule.mem_map.mpr ⟨A, A.property, rfl⟩)

@[simp] theorem gamma_conductorMatrix (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F))
    (A : matricesKilling (P := P) F) :
    alg.toCoefficients.gamma (alg.conductorMatrix F d A) =
      alg.toCoefficients.alpha A.val * d.val := by
  exact map_conductorLift _ alg.gamma_injective _ _ _

/-- Взаимность кондуктора для произвольного ограниченного пространства входов.
Ни гиперплоскость F, ни единица в A_F здесь не нужны. -/
theorem conductorMatrix_trace_reciprocity (alg : ExactAlgorithm K P Q S ι)
    (F : Submodule K (Q → K))
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F))
    (A A' : matricesKilling (P := P) F) (B : Matrix S Q K) :
    trace (B * A.val * alg.conductorMatrix F d A') =
      trace (B * A'.val * alg.conductorMatrix F d A) := by
  rw [trace_mul_comm (B * A.val), trace_mul_comm (B * A'.val),
    ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    alg.trace_identity, alg.trace_identity]
  apply Finset.sum_congr rfl
  intro i _
  have hA := congrFun (alg.gamma_conductorMatrix F d A) i
  have hA' := congrFun (alg.gamma_conductorMatrix F d A') i
  change trace (alg.W i * alg.conductorMatrix F d A) = _ at hA
  change trace (alg.W i * alg.conductorMatrix F d A') = _ at hA'
  rw [hA, hA']
  change _ * _ * (trace (alg.U i * A'.val) * d.val i) =
    _ * _ * (trace (alg.U i * A.val) * d.val i)
  ring

end ExactAlgorithm

/-- Гиперплоскость, заданная координатами ненулевой формы η; определение допускает η=0. -/
def coordinateHyperplane (η : Q → K) : Submodule K (Q → K) :=
  (dotProductBilin K K η).ker

/-- Вход u⊗η при правом действии: x ↦ (x·η)u. -/
noncomputable def hyperplaneInput (η : Q → K) :
    (P → K) →ₗ[K] matricesKilling (P := P) (coordinateHyperplane η) :=
  (vecMulVecBilin K K η).codRestrict _ fun u ↦ by
    apply (mem_matricesKilling _ _).mpr
    intro x hx
    change η ⬝ᵥ x = 0 at hx
    change x ᵥ* vecMulVec η u = 0
    rw [vecMul_vecMulVec, dotProduct_comm, hx, zero_smul]

omit [Fintype P] in
@[simp] theorem hyperplaneInput_val (η : Q → K) (u : P → K) :
    (hyperplaneInput η u).val = vecMulVec η u := rfl

/-- Ненулевая координатная форма имеет вектор со значением один. -/
theorem exists_dotProduct_eq_one (η : Q → K) (hη : η ≠ 0) :
    ∃ z : Q → K, z ⬝ᵥ η = 1 := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, η q ≠ 0 := Function.ne_iff.mp hη
  refine ⟨Pi.single q (η q)⁻¹, ?_⟩
  simp [hq]

omit [Fintype P] in
/-- Все входы, зануляющие ker η, имеют вид u⊗η. -/
theorem hyperplaneInput_surjective (η : Q → K) (hη : η ≠ 0) :
    Function.Surjective (hyperplaneInput (P := P) η) := by
  classical
  obtain ⟨z, hz⟩ := exists_dotProduct_eq_one η hη
  intro A
  refine ⟨z ᵥ* A.val, ?_⟩
  apply Subtype.ext
  ext q p
  have hx : Pi.single q 1 - η q • z ∈ coordinateHyperplane η := by
    change η ⬝ᵥ (Pi.single q 1 - η q • z) = 0
    rw [dotProduct_sub, dotProduct_single_one, dotProduct_smul,
      dotProduct_comm η z, hz]
    simp
  have ha := (mem_matricesKilling _ A.val).mp A.property hx
  change (Pi.single q 1 - η q • z) ᵥ* A.val = 0 at ha
  have he := congrFun ha p
  simp only [sub_vecMul, smul_vecMul, single_one_vecMul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
  exact (sub_eq_zero.mp he).symm

omit [Fintype P] in
/-- Ненулевая η параметризует ограниченные входы без избыточности. -/
theorem hyperplaneInput_injective (η : Q → K) (hη : η ≠ 0) :
    Function.Injective (hyperplaneInput (P := P) η) := by
  obtain ⟨q, hq⟩ : ∃ q, η q ≠ 0 := Function.ne_iff.mp hη
  intro u v huv
  funext p
  have h := congrArg (fun A ↦ (A : matricesKilling (P := P)
    (coordinateHyperplane η)).val q p) huv
  exact mul_left_cancel₀ hq h

/-- Любое подпространство коразмерности один задаётся ненулевой координатной формой. -/
theorem exists_coordinateHyperplane_of_finrank_add_one (F : Submodule K (Q → K))
    (hF : finrank K F + 1 = Fintype.card Q) :
    ∃ η : Q → K, η ≠ 0 ∧ F = coordinateHyperplane η := by
  classical
  have htop : F ≠ ⊤ := by
    intro hh
    rw [hh, finrank_top, Module.finrank_fintype_fun_eq_card] at hF
    omega
  obtain ⟨φ, hφ, hmap⟩ := F.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr htop) inferInstance
  obtain ⟨η, hηφ⟩ := (dotProductEquiv K Q).surjective φ
  have hη : η ≠ 0 := by
    intro h
    apply hφ
    rw [← hηφ, h, map_zero]
  refine ⟨η, hη, ?_⟩
  have hle : F ≤ φ.ker := by
    intro x hx
    have hh : φ x ∈ F.map φ := Submodule.mem_map_of_mem hx
    simpa [hmap] using hh
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  rw [Module.finrank_fintype_fun_eq_card] at hk
  have he : F = φ.ker := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [he, ← hηφ]
  rfl

namespace ExactAlgorithm

/-- Симметрия в физических направлениях u,v; верна также в характеристике два. -/
theorem conductorMatrix_hyperplane_reciprocity [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0)
    (d : conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) (u v : P → K) :
    v ᵥ* alg.conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η u) =
      u ᵥ* alg.conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η v) := by
  classical
  obtain ⟨z, hz⟩ := exists_dotProduct_eq_one η hη
  ext s
  have h := alg.conductorMatrix_trace_reciprocity (coordinateHyperplane η) d
    (hyperplaneInput η v) (hyperplaneInput η u) (vecMulVec (Pi.single s 1) z)
  simpa only [hyperplaneInput_val, vecMulVec_mul_vecMulVec, hz, one_smul,
    vecMulVec_mul, trace_vecMulVec, single_dotProduct, one_mul,
    vecMul_vecMulVec, hz, one_smul] using h

/-- Физическая оболочка порождена матрицами C_d(u⊗η). -/
theorem conductorPhysicalSpace_eq_span_hyperplane [Nonempty Q]
    (alg : ExactAlgorithm K P Q S ι) (η : Q → K) (hη : η ≠ 0) :
    conductorPhysicalSpace alg.toCoefficients.gamma
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)) =
      Submodule.span K (Set.range fun p :
        conductor alg.toCoefficients.gamma.range
          (alg.toCoefficients.alphaOn (coordinateHyperplane η)) × (P → K) ↦
        alg.conductorMatrix (coordinateHyperplane η) p.1 (hyperplaneInput η p.2)) := by
  rw [conductorPhysicalSpace_eq_span _ alg.gamma_injective]
  congr 1
  ext C
  constructor
  · rintro ⟨⟨m, d⟩, rfl⟩
    obtain ⟨A, hA, ha⟩ := Submodule.mem_map.mp m.property
    obtain ⟨u, hu⟩ := hyperplaneInput_surjective (P := P) η hη ⟨A, hA⟩
    refine ⟨(d, u), ?_⟩
    apply alg.gamma_injective
    rw [gamma_conductorMatrix, map_conductorLift, hu]
    exact congrArg (fun a ↦ a * d.val) ha
  · rintro ⟨⟨d, u⟩, rfl⟩
    exact ⟨(⟨alg.toCoefficients.alpha (hyperplaneInput η u).val,
      Submodule.mem_map.mpr ⟨_, (hyperplaneInput η u).property, rfl⟩⟩, d), rfl⟩

end ExactAlgorithm
end MMRank
