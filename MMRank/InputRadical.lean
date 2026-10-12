module

public import MMRank.AlgorithmReflection
public import MMRank.SupportedTestParameters

@[expose] public section

/-! # Радикал подстановки и пространство поддержанных тестов -/

namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Входы B со значениями в F, на которых все внешние βᵢ равны нулю. -/
def Coefficients.inputRadical (d : Coefficients K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I) : Submodule K (Matrix S Q K) :=
  matricesInto F ⊓ (coordinateSection K d.beta.range G).comap d.beta

omit [Fintype P] [Fintype I] in
@[simp] theorem Coefficients.mem_inputRadical (d : Coefficients K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I) (B : Matrix S Q K) :
    B ∈ d.inputRadical F G ↔ B ∈ matricesInto F ∧ ∀ i ∉ G, d.beta B i = 0 := by
  change (B ∈ matricesInto F ∧ d.beta B ∈ coordinateSection K d.beta.range G) ↔ _
  rw [mem_coordinateSection]
  exact and_congr_right (fun _ ↦ and_iff_right ⟨B, rfl⟩)

/-- Оценка вторых форм на внешних индексах, ограниченная входами в F. -/
def Coefficients.externalBeta (d : Coefficients K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I) : matricesInto (S := S) F →ₗ[K] (↥(Gᶜ) → K) :=
  LinearMap.pi (fun i ↦ (LinearMap.proj i.val).comp (d.beta.domRestrict (matricesInto F)))

omit [Fintype P] [Fintype I] in
theorem Coefficients.finrank_externalBeta_add_radical (d : Coefficients K P Q S I)
    (F : Submodule K (Q → K)) (G : Set I) :
    finrank K (d.externalBeta F G).range + finrank K (d.inputRadical F G) =
      Fintype.card S * finrank K F := by
  have hk : (d.externalBeta F G).ker =
      (d.inputRadical F G).comap (matricesInto (S := S) F).subtype := by
    ext B
    change ((fun i : ↥(Gᶜ) ↦ d.beta B.val i.val) = 0) ↔ B.val ∈ d.inputRadical F G
    simp only [funext_iff, Pi.zero_apply]
    rw [Coefficients.mem_inputRadical]
    simp only [B.property, true_and]
    exact ⟨fun h i hi ↦ h ⟨i, hi⟩, fun h i ↦ h i i.property⟩
  have hh := (d.externalBeta F G).finrank_range_add_finrank_ker
  rw [hk, ← Submodule.finrank_map_subtype_eq (matricesInto (S := S) F),
    Submodule.map_comap_subtype] at hh
  have hle : d.inputRadical F G ≤ matricesInto (S := S) F := inf_le_left
  rw [inf_eq_right.mpr hle, finrank_matricesInto] at hh
  exact hh

/-- Параметры простого теста переходят в радикал отражённого алгоритма
по s↦(p⊗s)ᵀ. Точность для этого изоморфизма не нужна. -/
noncomputable def Coefficients.testParameterRadicalEquiv
    (d : Coefficients K P Q S I) (p : P → K) (hp : p ≠ 0) (G : Set I) :
    d.supportedTestParameters p G ≃ₗ[K] d.reflect.inputRadical (Submodule.span K {p}) G := by
  let f := ((Matrix.transposeLinearEquiv P S K K).toLinearMap.comp (vecMulVecBilin K K p)).domRestrict
    (d.supportedTestParameters p G)
  have hf (s : d.supportedTestParameters p G) : f s ∈ d.reflect.inputRadical (Submodule.span K {p}) G := by
    rw [mem_inputRadical]
    refine ⟨?_, ?_⟩
    · exact (transpose_mem_matricesInto_span_iff p (vecMulVec p s.val)).mpr ⟨s.val, rfl⟩
    · intro i hi
      change d.reflect.beta (vecMulVec p s.val).transpose i = 0
      rw [beta_reflect, transpose_transpose]
      exact (mem_supportedTestParameters _ _ _ _).mp s.property i hi
  apply LinearEquiv.ofBijective (f.codRestrict _ hf)
  constructor
  · intro s t h
    apply Subtype.ext
    apply fixedColumnMap_injective hp
    apply Matrix.transpose_injective
    exact congrArg Subtype.val h
  · intro B
    have hB := (mem_inputRadical _ _ _ _).mp B.property
    obtain ⟨s, hs⟩ := (transpose_mem_matricesInto_span_iff p B.val.transpose).mp
      (by simpa only [transpose_transpose] using hB.1)
    change vecMulVec p s = B.val.transpose at hs
    refine ⟨⟨s, ?_⟩, ?_⟩
    · rw [mem_supportedTestParameters]
      intro i hi
      rw [hs, ← beta_reflect]
      exact hB.2 i hi
    · apply Subtype.ext
      change (vecMulVec p s).transpose = B.val
      rw [hs, transpose_transpose]

/-- Сечение выходных тестов изоморфно радикалу при полном первом
столбцовом пространстве; квадратность размеров не требуется. -/
noncomputable def ExactAlgorithm.supportedTestRadicalEquiv [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (p : P → K) (hp : p ≠ 0) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p) :
    coordinateSection K alg.toCoefficients.gamma.range G ≃ₗ[K]
      alg.reflect.toCoefficients.inputRadical (Submodule.span K {p}) G :=
  (alg.supportedTestWordEquiv p hp G hspan).symm.trans
    (alg.toCoefficients.testParameterRadicalEquiv p hp G)

end MMRank
