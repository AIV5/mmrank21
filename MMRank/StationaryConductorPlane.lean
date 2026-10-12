module

public import MMRank.MatrixColumnCore
public import MMRank.ReciprocalColumnSpace
public import MMRank.ConductorWordRank
public import MMRank.PointWordPhysical

@[expose] public section

namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Полная свёртка поддержанных тестов помещает их колонковую оболочку
в постоянное ядро полного матричного модуля U_G. -/
theorem ExactAlgorithm.columnSpan_le_core_of_supported (alg : ExactAlgorithm K P Q S I)
    (G : Set I) (T : Submodule K (Matrix P S K))
    (hT : ∀ C ∈ T, ∀ i ∉ G, alg.toCoefficients.gamma C i = 0) :
    matrixColumnSpan T ≤ matrixColumnCore (Submodule.span K (alg.U '' G)) := by
  apply iSup_le
  intro C
  rintro p ⟨v, rfl⟩ q
  have hh := alg.mul_mem_span_of_gamma_supported G C.val (hT C.val C.property) (vecMulVec v q)
  simpa only [mul_vecMulVec, Matrix.vecMulLinear_apply, vecMul_transpose] using hh

/-- На носителе слова значения U_iη лежат в колонковой оболочке его
симметричного физического семейства, до какого-либо общего выбора. -/
theorem ExactAlgorithm.conductor_evaluation_mem_columnSpan [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (i : I) (hi : d.val i ≠ 0) :
    alg.U i *ᵥ η ∈ matrixColumnSpan
      ((alg.conductorMatrix (coordinateHyperplane η) d).comp (hyperplaneInput η)).range := by
  let C := (alg.conductorMatrix (coordinateHyperplane η) d).comp (hyperplaneInput η)
  have hsym (x y : P → K) : x ᵥ* C y = y ᵥ* C x :=
    (alg.conductorMatrix_hyperplane_reciprocity η hη d x y).symm
  rw [reciprocal_columnSpan_eq_orthogonal_ker C hsym]
  intro x hx
  have hz : C x = 0 := hx
  have hh := congrFun (alg.gamma_conductorMatrix (coordinateHyperplane η) d (hyperplaneInput η x)) i
  change alg.toCoefficients.gamma (C x) i =
    alg.toCoefficients.alpha (hyperplaneInput η x).val i * d.val i at hh
  rw [hz, map_zero, Pi.zero_apply, Coefficients.alpha_hyperplaneInput_apply] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_right hi

/-- При доказанной общности η вся оболочка U на носителе слова имеет
постоянное колонковое пространство той же размерности, что и A_F d.
Ранг2 не предполагается: результат общий для любого слова кондуктора. -/
theorem ExactAlgorithm.conductor_support_stationary_columns [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (hgen : MatrixColumnGeneric alg.U η)
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) :
    ∃ F : Submodule K (P → K),
      finrank K F = finrank K ((alg.toCoefficients.alphaOn (coordinateHyperplane η)).map
        (LinearMap.mulRight K d.val)) ∧
      (∀ i, d.val i ≠ 0 → (alg.U i).transpose ∈ matricesInto (S := Q) F) ∧
      F = matrixColumnCore (Submodule.span K (alg.U '' {i | d.val i ≠ 0})) := by
  classical
  let G : Set I := {i | d.val i ≠ 0}
  let C := (alg.conductorMatrix (coordinateHyperplane η) d).comp (hyperplaneInput η)
  let F := matrixColumnSpan C.range
  let E := Submodule.span K (alg.U '' G)
  have hsupp (D : Matrix P S K) (hD : D ∈ C.range) :
      ∀ i ∉ G, alg.toCoefficients.gamma D i = 0 := by
    obtain ⟨x, rfl⟩ := hD
    intro i hi
    have hd : d.val i = 0 := by simpa [G] using hi
    change alg.toCoefficients.gamma (alg.conductorMatrix _ d (hyperplaneInput η x)) i = 0
    rw [alg.gamma_conductorMatrix]
    simp [hd]
  have hFcore : F ≤ matrixColumnCore E := alg.columnSpan_le_core_of_supported G C.range hsupp
  have hval (i) (hi : i ∈ G) : alg.U i *ᵥ η ∈ F :=
    alg.conductor_evaluation_mem_columnSpan η hη d i hi
  have heval : E.map (Matrix.mulVecBilin K K |>.flip η) ≤ F := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hval i hi
  have hcore : matrixColumnCore E = F :=
    le_antisymm ((matrixColumnCore_le_evaluation E η hη).trans heval) hFcore
  have hsym (x y : P → K) : x ᵥ* C y = y ᵥ* C x :=
    (alg.conductorMatrix_hyperplane_reciprocity η hη d x y).symm
  have hr : C.range = (alg.conductorMatrix (coordinateHyperplane η) d).range := by
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (hyperplaneInput_surjective η hη))
  refine ⟨F, ?_, ?_, hcore.symm⟩
  · rw [finrank_reciprocal_columnSpan C hsym, hr, alg.finrank_conductorMatrix_range]
  · intro i hi
    apply (mem_matricesInto F _).mpr
    rintro _ ⟨x, rfl⟩
    have hh := hgen G i hi (hFcore (hval i hi)) x
    rw [hcore] at hh
    simpa only [Matrix.vecMulLinear_apply, vecMul_transpose] using hh

/-- Оболочка коэффициентов на носителе слова — именно полный колонковый
модуль, а не только его подпространство. Размеры и ранг слова произвольны. -/
theorem ExactAlgorithm.conductor_support_span_full_columns [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (hgen : MatrixColumnGeneric alg.U η)
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) :
    ∃ F : Submodule K (P → K),
      finrank K F = finrank K ((alg.toCoefficients.alphaOn (coordinateHyperplane η)).map
        (LinearMap.mulRight K d.val)) ∧
      Submodule.span K (alg.U '' {i | d.val i ≠ 0}) =
        (matricesInto (S := Q) F).map (transposeLinearEquiv Q P K K).toLinearMap := by
  obtain ⟨F, hd, hcols, hcore⟩ := alg.conductor_support_stationary_columns η hη hgen d
  refine ⟨F, hd, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨(alg.U i).transpose, hcols i hi, transpose_transpose _⟩
  · exact matricesColumns_le_of_le_core _ F hcore.le

/-- Точная размерность оболочки первых коэффициентов на носителе слова. -/
theorem ExactAlgorithm.finrank_conductor_support_span [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (hgen : MatrixColumnGeneric alg.U η)
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) :
    finrank K (Submodule.span K (alg.U '' {i | d.val i ≠ 0})) =
      Fintype.card Q * finrank K ((alg.toCoefficients.alphaOn (coordinateHyperplane η)).map
        (LinearMap.mulRight K d.val)) := by
  obtain ⟨F, hd, he⟩ := alg.conductor_support_span_full_columns η hη hgen d
  rw [he, LinearEquiv.finrank_map_eq, finrank_matricesInto, hd]

end MMRank
