module

public import MMRank.MatrixSubspaceGeneric
public import MMRank.FixedColumnSpace
public import MMRank.TraceDuality

@[expose] public section

namespace MMRank
open Matrix Module MvPolynomial
variable {K P Q I : Type*} [Field K]

/-- Наибольшее пространство первых факторов, чей полный матричный модуль
содержится в S. Определение не зависит от выбранного η. -/
def matrixColumnCore (S : Submodule K (Matrix P Q K)) : Submodule K (P → K) where
  carrier := {p | ∀ q : Q → K, vecMulVec p q ∈ S}
  zero_mem' := by simp
  add_mem' := by intro p r hp hr q; simpa only [add_vecMulVec] using S.add_mem (hp q) (hr q)
  smul_mem' := by intro a p hp q; simpa only [smul_vecMulVec] using S.smul_mem a (hp q)

/-- Полный модуль даёт все значения первого фактора в любой ненулевой точке. -/
theorem matrixColumnCore_le_evaluation [Fintype Q]
    (S : Submodule K (Matrix P Q K)) (η : Q → K) (hη : η ≠ 0) :
    matrixColumnCore S ≤ S.map (Matrix.mulVecBilin K K |>.flip η) := by
  obtain ⟨q, hq⟩ := exists_dotProduct_eq_one η hη
  intro p hp
  refine ⟨vecMulVec p q, hp q, ?_⟩
  change vecMulVec p q *ᵥ η = p
  simp [vecMulVec_mulVec, hq]

/-- Полный колонковый модуль размерности q·dim F содержится в S. -/
theorem matricesColumns_le_of_le_core [Fintype Q]
    (S : Submodule K (Matrix P Q K)) (F : Submodule K (P → K))
    (hF : F ≤ matrixColumnCore S) :
    (matricesInto (S := Q) F).map (transposeLinearEquiv Q P K K).toLinearMap ≤ S := by
  classical
  rintro _ ⟨A, ⟨b, rfl⟩, rfl⟩
  have he : (rowsInclusion F b).transpose = ∑ q, vecMulVec (b q).val (Pi.single q 1) := by
    ext p q
    change (b q).val p = (∑ j, vecMulVec (b j).val (Pi.single j 1)) p q
    simp [Matrix.sum_apply, vecMulVec, Pi.single_apply]
  change (rowsInclusion F b).transpose ∈ S
  rw [he]
  exact Submodule.sum_mem _ (fun q _ ↦ hF (b q).property _)

/-- Общее значение не попадает в постоянное ядро полного модуля случайно. -/
def MatrixColumnGeneric [Fintype Q] (U : I → Matrix P Q K) (η : Q → K) : Prop :=
  ∀ G : Set I, ∀ i ∈ G,
    U i *ᵥ η ∈ matrixColumnCore (Submodule.span K (U '' G)) →
    ∀ x, U i *ᵥ x ∈ matrixColumnCore (Submodule.span K (U '' G))

/-- Покомпонентное ненулевое масштабирование сохраняет оболочки всех групп. -/
theorem span_image_smul_eq (U : I → Matrix P Q K) (c : I → K)
    (hc : ∀ i, c i ≠ 0) (G : Set I) :
    Submodule.span K ((fun i ↦ c i • U i) '' G) = Submodule.span K (U '' G) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hm := Submodule.smul_mem (Submodule.span K ((fun i ↦ c i • U i) '' G)) (c i)⁻¹
      (Submodule.subset_span ⟨i, hi, rfl⟩)
    simpa [smul_smul, hc i] using hm

theorem matrixColumnGeneric_smul_iff [Fintype Q] (U : I → Matrix P Q K)
    (c : I → K) (hc : ∀ i, c i ≠ 0) (η : Q → K) :
    MatrixColumnGeneric (fun i ↦ c i • U i) η ↔ MatrixColumnGeneric U η := by
  have hm (G : Set I) (i : I) (x : Q → K) :
      (c i • U i) *ᵥ x ∈ matrixColumnCore (Submodule.span K ((fun i ↦ c i • U i) '' G)) ↔
        U i *ᵥ x ∈ matrixColumnCore (Submodule.span K (U '' G)) := by
    rw [span_image_smul_eq U c hc, smul_mulVec]
    exact Submodule.smul_mem_iff _ (hc i)
  simp only [MatrixColumnGeneric, hm]

end MMRank
