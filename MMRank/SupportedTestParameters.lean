import MMRank.FixedColumnTransport
import MMRank.SupportedTestSpan
import MMRank.CoordinateDecomposition

/-! # Параметры пространства поддержанных выходных тестов -/

namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Строки s, для которых γ(p⊗s) зануляется вне G. -/
def Coefficients.supportedTestParameters (d : Coefficients K P Q S I)
    (p : P → K) (G : Set I) : Submodule K (S → K) :=
  (coordinateSection K d.gamma.range G).comap (d.gamma.comp (vecMulVecBilin K K p))

omit [Fintype Q] [Fintype I] in
@[simp] theorem Coefficients.mem_supportedTestParameters
    (d : Coefficients K P Q S I) (p : P → K) (G : Set I) (s : S → K) :
    s ∈ d.supportedTestParameters p G ↔ ∀ i ∉ G, d.gamma (vecMulVec p s) i = 0 := by
  change (d.gamma (vecMulVec p s) ∈ coordinateSection K d.gamma.range G) ↔ _
  rw [mem_coordinateSection]
  exact and_iff_right ⟨_, rfl⟩

namespace ExactAlgorithm

/-- Любой тест на G имеет тот же первый фактор, если оболочка U_G
лежит в фиксированном столбцовом пространстве. -/
theorem test_mem_fixedColumnSpace [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (p : P → K) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p)
    (C : Matrix P S K) (hC : ∀ i ∉ G, alg.toCoefficients.gamma C i = 0) :
    C ∈ fixedColumnSpace (Q := S) p := by
  apply mem_fixedColumnSpace_of_mul_mem (Q := Q) p C
  intro B
  exact hspan (alg.mul_mem_span_of_gamma_supported G C hC B)

/-- Поддержанные тестовые строки и внутреннее координатное сечение γ
линейно изоморфны. Проектор на G не предполагается сохраняющим imγ. -/
noncomputable def supportedTestWordEquiv [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (p : P → K) (hp : p ≠ 0) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p) :
    alg.toCoefficients.supportedTestParameters p G ≃ₗ[K]
      coordinateSection K alg.toCoefficients.gamma.range G := by
  let f := (alg.toCoefficients.gamma.comp (vecMulVecBilin K K p)).domRestrict
    (alg.toCoefficients.supportedTestParameters p G)
  let g := f.codRestrict (coordinateSection K alg.toCoefficients.gamma.range G)
    (fun s ↦ s.property)
  apply LinearEquiv.ofBijective g
  constructor
  · intro s t h
    apply Subtype.ext
    apply fixedColumnMap_injective hp
    apply alg.gamma_injective
    exact congrArg Subtype.val h
  · intro w
    obtain ⟨C, hC⟩ := w.property.1
    have hsupp : ∀ i ∉ G, alg.toCoefficients.gamma C i = 0 := by
      rw [hC]
      exact (mem_coordinateSection.mp w.property).2
    obtain ⟨s, hs⟩ := alg.test_mem_fixedColumnSpace p G hspan C hsupp
    refine ⟨⟨s, ?_⟩, ?_⟩
    · rw [Coefficients.mem_supportedTestParameters]
      change ∀ i ∉ G, alg.toCoefficients.gamma ((vecMulVecBilin K K p) s) i = 0
      rwa [hs]
    · apply Subtype.ext
      change alg.toCoefficients.gamma ((vecMulVecBilin K K p) s) = w.val
      rw [hs, hC]

theorem finrank_supportedTestParameters [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (p : P → K) (hp : p ≠ 0) (G : Set I)
    (hspan : Submodule.span K (alg.U '' G) ≤ fixedColumnSpace (Q := Q) p) :
    finrank K (alg.toCoefficients.supportedTestParameters p G) =
      finrank K (coordinateSection K alg.toCoefficients.gamma.range G) :=
  (alg.supportedTestWordEquiv p hp G hspan).finrank_eq

end ExactAlgorithm
end MMRank
