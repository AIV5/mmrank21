module

public import MMRank.SupportedTestMass
public import MMRank.RectangularCompression
public import MMRank.AnnihilatorCapacity
public import MMRank.ConductorOrthogonality

@[expose] public section

namespace MMRank
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Все физические тесты, чьи слова поддержаны на G. -/
def Coefficients.supportedTests (d : Coefficients K P Q S I) (G : Set I) :
    Submodule K (Matrix P S K) := (coordinateSection K d.gamma.range G).comap d.gamma

omit [Fintype Q] [Fintype I] in
@[simp] theorem Coefficients.mem_supportedTests (d : Coefficients K P Q S I)
    (G : Set I) (C : Matrix P S K) :
    C ∈ d.supportedTests G ↔ ∀ i ∉ G, d.gamma C i = 0 := by
  change d.gamma C ∈ coordinateSection K d.gamma.range G ↔ _
  rw [mem_coordinateSection]
  exact and_iff_right ⟨C, rfl⟩

/-- Совместный образ физических тестов при правом действии. -/
def Coefficients.supportedTestImage (d : Coefficients K P Q S I) (G : Set I) :
    Submodule K (S → K) := ⨆ C : d.supportedTests G, C.val.vecMulLinear.range

namespace ExactAlgorithm

noncomputable def supportedTestsEquiv [Nonempty Q] (alg : ExactAlgorithm K P Q S I)
    (G : Set I) : alg.toCoefficients.supportedTests G ≃ₗ[K]
      coordinateSection K alg.toCoefficients.gamma.range G := by
  apply LinearEquiv.ofBijective
    ((alg.toCoefficients.gamma.domRestrict _).codRestrict _ (fun C ↦ C.property))
  constructor
  · intro C D h
    exact Subtype.ext (alg.gamma_injective (congrArg Subtype.val h))
  · intro w
    obtain ⟨C, hC⟩ := w.property.1
    exact ⟨⟨C, by change alg.toCoefficients.gamma C ∈ coordinateSection K alg.toCoefficients.gamma.range G; rw [hC]; exact w.property⟩,
      Subtype.ext hC⟩

/-- Каждый столбец поддержанного теста лежит в F, если это верно для U_G. -/
theorem supportedTests_columns [Nonempty Q] (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (P → K)) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F)
    (C : alg.toCoefficients.supportedTests G) :
    C.val.transpose ∈ matricesInto (S := S) F := by
  classical
  have hspan : Submodule.span K (alg.U '' G) ≤
      (matricesInto (S := Q) F).comap (transposeLinearEquiv P Q K K).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hG i hi
  let q : Q := Classical.arbitrary Q
  apply (mem_matricesInto F _).mpr
  rw [range_vecMulLinear, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  have hh := hspan (alg.mul_mem_span_of_gamma_supported G C.val
    ((Coefficients.mem_supportedTests _ _ _).mp C.property) (single s q 1))
  have hr := (mem_matricesInto F _).mp hh
  have hm := hr (show ((C.val * single s q (1 : K)).transpose) q ∈
      ((C.val * single s q (1 : K)).transpose).vecMulLinear.range from by
    rw [range_vecMulLinear]; exact Submodule.subset_span (Set.mem_range_self q))
  have he : ((C.val * single s q (1 : K)).transpose) q = C.val.transpose s := by
    ext p
    simp
  rwa [he] at hm

/-- Оболочка соседних коэффициентов содержит все строки совместного образа. -/
theorem matricesInto_supportedTestImage_le_span (alg : ExactAlgorithm K P Q S I)
    (G : Set I) : matricesInto (S := Q) (alg.toCoefficients.supportedTestImage G) ≤
      Submodule.span K (alg.V '' G) := by
  classical
  let E := Submodule.span K (alg.V '' G)
  have hv (y : Q → K) (s : S → K) (hs : s ∈ alg.toCoefficients.supportedTestImage G) :
      vecMulVec y s ∈ E := by
    have hle : alg.toCoefficients.supportedTestImage G ≤
        E.comap (vecMulVecBilin K K y) := by
      apply iSup_le
      intro C
      rintro _ ⟨x, rfl⟩
      have hh := alg.left_mul_mem_span_of_gamma_supported G C.val
        ((Coefficients.mem_supportedTests _ _ _).mp C.property) (vecMulVec y x)
      change vecMulVec y (x ᵥ* C.val) ∈ E
      simpa only [vecMulVec_mul] using hh
    exact hle hs
  rintro _ ⟨b, rfl⟩
  have he : rowsInclusion (S := Q) (alg.toCoefficients.supportedTestImage G) b =
      ∑ q, vecMulVec (Pi.single q 1) (b q).val := by
    ext i j
    change (b i).val j = (∑ q, vecMulVec (Pi.single q 1) (b q).val) i j
    simp [Matrix.sum_apply, vecMulVec, Pi.single_apply]
  rw [he]
  exact Submodule.sum_mem _ (fun q _ ↦ hv _ _ (b q).property)

theorem supportedTestImage_mass (alg : ExactAlgorithm K P Q S I) (G : Set I) :
    Fintype.card Q * finrank K (alg.toCoefficients.supportedTestImage G) ≤
      finrank K (Submodule.span K (alg.V '' G)) := by
  simpa only [finrank_matricesInto] using
    Submodule.finrank_mono (alg.matricesInto_supportedTestImage_le_span G)

/-- Вместимость тестов с колонками в F и строками в их совместном образе. -/
theorem supportedTests_capacity [Nonempty Q] (alg : ExactAlgorithm K P Q S I)
    (F : Submodule K (P → K)) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F) :
    finrank K (alg.toCoefficients.supportedTests G) ≤
      finrank K F * finrank K (alg.toCoefficients.supportedTestImage G) := by
  let f := rowLinearEquiv.toLinearMap.comp (alg.toCoefficients.supportedTests G).subtype
  have hr (C : alg.toCoefficients.supportedTests G) :
      (f C).range ≤ alg.toCoefficients.supportedTestImage G := by
    dsimp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [rowLinearEquiv_apply]
    exact le_iSup (fun D : alg.toCoefficients.supportedTests G ↦ D.val.vecMulLinear.range) C
  have hk (C : alg.toCoefficients.supportedTests G) :
      F.orthogonalBilin (dotProductBilin K K) ≤ (f C).ker := by
    intro x hx
    have hcols := (mem_matricesInto F _).mp (alg.supportedTests_columns F G hG C)
    change (rowLinearEquiv C.val) x = 0
    rw [rowLinearEquiv_apply]
    ext s
    change x ⬝ᵥ C.val.transpose s = 0
    simpa only [dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_comm] using
      hx _ (hcols (by rw [range_vecMulLinear]; exact Submodule.subset_span (Set.mem_range_self s)))
  have hb := finrank_le_annihilator_capacity _ _ f
    (rowLinearEquiv.injective.comp (Submodule.injective_subtype _)) hr hk
  have hd := finrank_coordinateOrthogonal F
  have hf := Submodule.finrank_le F
  change finrank K (Submodule.orthogonalBilin (dotProductBilin K K) F) = _ at hd
  simp only [Module.finrank_fintype_fun_eq_card] at hb hf
  rw [hd, Nat.sub_sub_self hf] at hb
  exact hb

end ExactAlgorithm
end MMRank
