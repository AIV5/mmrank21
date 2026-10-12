import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Следовое представление линейных форм и свидетели неполноты

Прямоугольные матрицы спариваются как tr(VB), без деления на размер.
Представление линейной формы работает над полукольцом; отделение собственного
подпространства требует тела, но не бесконечности или коммутативности.
-/

namespace MMRank

variable {K Q S : Type*} [Fintype Q] [Fintype S]

/-- Каждая левая линейная форма единственным образом имеет вид V ↦ tr(VB). -/
theorem exists_unique_trace_representation [Semiring K]
    (f : (Matrix Q S K) →ₗ[K] K) :
    ∃! B : Matrix S Q K, ∀ V, f V = Matrix.trace (V * B) := by
  classical
  let B : Matrix S Q K := fun s q ↦ f (Matrix.single q s 1)
  have he : f = (Matrix.traceLinearMap Q K K).comp (mulRightLinearMap Q K B) := by
    apply Matrix.ext_linearMap
    intro q s
    apply LinearMap.ext_ring
    change f (Matrix.single q s 1) = Matrix.trace (Matrix.single q s (1 : K) * B)
    rw [Matrix.trace_single_mul q s (1 : K) B, one_smul]
  have hB : ∀ V, f V = Matrix.trace (V * B) := fun V ↦ DFunLike.congr_fun he V
  refine ⟨B, hB, ?_⟩
  intro C hC
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro V
  exact (hC V).symm.trans (hB V)

/-- У собственного подпространства матриц есть ненулевой следовой аннулятор. -/
theorem exists_nonzero_trace_annihilator [DivisionRing K]
    (T : Submodule K (Matrix Q S K)) (hT : T ≠ ⊤) :
    ∃ B : Matrix S Q K, B ≠ 0 ∧ ∀ V ∈ T, Matrix.trace (V * B) = 0 := by
  obtain ⟨f, hf, hTf⟩ := T.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hT) inferInstance
  obtain ⟨B, hB, _⟩ := exists_unique_trace_representation f
  refine ⟨B, ?_, ?_⟩
  · intro hzero
    apply hf
    ext V
    simp [hB V, hzero]
  · intro V hV
    rw [← hB V]
    have hm : f V ∈ T.map f := Submodule.mem_map_of_mem hV
    simpa [hTf] using hm

/-- Порождающее семейство матриц не имеет ненулевого следового аннулятора. -/
theorem eq_zero_of_trace_annihilates_spanning [Semiring K]
    {s : Set (Matrix Q S K)} (hs : Submodule.span K s = ⊤)
    (B : Matrix S Q K) (hB : ∀ V ∈ s, Matrix.trace (V * B) = 0) : B = 0 := by
  let f := (Matrix.traceLinearMap Q K K).comp (mulRightLinearMap Q K B)
  have hker : Submodule.span K s ≤ f.ker := Submodule.span_le.mpr hB
  rw [hs] at hker
  have hf : f = 0 := LinearMap.ker_eq_top.mp (top_unique hker)
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro V
  have hv := DFunLike.congr_fun hf V
  simpa [f] using hv

/-- Если матрицы с ненулевыми весами порождают всё пространство, нулевые
взвешенные следовые произведения вынуждают B = 0. Конечность индексов не нужна. -/
theorem eq_zero_of_weighted_trace_products [Semiring K] [NoZeroDivisors K]
    {ι : Type*} (V : ι → Matrix Q S K) (w : ι → K)
    (hs : Submodule.span K (V '' {i | w i ≠ 0}) = ⊤)
    (B : Matrix S Q K) (hB : ∀ i, w i * Matrix.trace (V i * B) = 0) : B = 0 := by
  apply eq_zero_of_trace_annihilates_spanning hs B
  rintro _ ⟨i, hi, rfl⟩
  exact (mul_eq_zero.mp (hB i)).resolve_left hi

end MMRank
