import MMRank.MatrixColumnCore
import MMRank.SupportedTestSpan
import MMRank.FixedColumnTransport

/-! # Поддержанный простой тест и общность столбцового ядра

Полная коэффициентная оболочка восстанавливается из одного значения U_iη=p.
Общность направлений и классификация поточечно коллинеарных отображений
не требуются. Размеры и характеристика поля произвольны.
-/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Если поддержанный простой тест имеет постоянное ненулевое последнее
направление, а все поддержанные U_iη равны p, общность столбцового ядра
даёт всю оболочку p⊗K^Q. Сам первый фактор p допускается нулевым. -/
theorem span_eq_fixedColumnSpace_of_column_generic
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (hgen : MatrixColumnGeneric alg.U η)
    (G : Set I) (p : P → K) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (hu : ∀ i ∈ G, alg.U i *ᵥ η = p) :
    Submodule.span K (alg.U '' G) = fixedColumnSpace (Q := Q) p := by
  let E := Submodule.span K (alg.U '' G)
  have hfull : fixedColumnSpace (Q := Q) p ≤ E :=
    alg.fixedColumnSpace_le_span_of_gamma_supported G p s hs hG
  have hp : p ∈ matrixColumnCore E := by
    intro q
    exact hfull ⟨q, rfl⟩
  have hval : E.map (Matrix.mulVecBilin K K |>.flip η) ≤ Submodule.span K {p} := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    change alg.U i *ᵥ η ∈ Submodule.span K {p}
    rw [hu i hi]
    exact Submodule.mem_span_singleton_self p
  have hcore := (matrixColumnCore_le_evaluation E η hη).trans hval
  refine le_antisymm (Submodule.span_le.mpr ?_) hfull
  rintro _ ⟨i, hi, rfl⟩
  apply (transpose_mem_matricesInto_span_iff p (alg.U i)).mp
  apply (mem_matricesInto (Submodule.span K {p}) _).mpr
  rintro _ ⟨x, rfl⟩
  have hh := hgen G i hi (by rw [hu i hi]; exact hp) x
  simpa only [Matrix.vecMulLinear_apply, vecMul_transpose] using hcore hh

end MMRank.ExactAlgorithm
