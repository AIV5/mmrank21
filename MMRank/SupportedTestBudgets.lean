import MMRank.SupportedTestSpace
import MMRank.RestrictedRankBudget

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Отражённый радикал — все поддержанные тесты, а не только простые. -/
noncomputable def supportedTestsRadicalEquiv [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (F : Submodule K (P → K)) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F) :
    alg.toCoefficients.supportedTests G ≃ₗ[K] alg.reflect.toCoefficients.inputRadical F G := by
  let f := (transposeLinearEquiv P S K K).toLinearMap.domRestrict
    (alg.toCoefficients.supportedTests G)
  have hf (C : alg.toCoefficients.supportedTests G) :
      f C ∈ alg.reflect.toCoefficients.inputRadical F G := by
    rw [Coefficients.mem_inputRadical]
    refine ⟨alg.supportedTests_columns F G hG C, ?_⟩
    intro i hi
    change alg.toCoefficients.reflect.beta C.val.transpose i = 0
    rw [Coefficients.beta_reflect, transpose_transpose]
    exact (Coefficients.mem_supportedTests _ _ _).mp C.property i hi
  apply LinearEquiv.ofBijective (f.codRestrict _ hf)
  constructor
  · intro C D h
    exact Subtype.ext (transpose_injective (congrArg Subtype.val h))
  · intro B
    have hb := (Coefficients.mem_inputRadical _ _ _ _).mp B.property
    refine ⟨⟨B.val.transpose, ?_⟩, Subtype.ext (transpose_transpose B.val)⟩
    rw [Coefficients.mem_supportedTests]
    intro i hi
    rw [← Coefficients.beta_reflect]
    exact hb.2 i hi

/-- Любая фиксированная колонковая группа оплачивает прямоугольный спуск.
Достаточна выходная развёртка остатка; точек и нормировки не требуется. -/
theorem supportedTests_exterior_budget [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (F : Submodule K (P → K)) (G : Set I)
    (hG : ∀ i ∈ G, (alg.U i).transpose ∈ matricesInto (S := Q) F)
    (hF : finrank K F < Fintype.card P) :
    G.ncard + Fintype.card Q * Fintype.card S + Fintype.card S * finrank K F ≤
      Fintype.card I + finrank K (alg.toCoefficients.supportedTests G) := by
  classical
  have hb := alg.reflect.exterior_pair_budget F G hG
  rw [← (alg.supportedTestsRadicalEquiv F G hG).finrank_eq] at hb
  obtain ⟨n, ⟨rect⟩, hn⟩ := alg.reflect.exists_rectangular_compression F G hG
  have hquot : 0 < finrank K ((P → K) ⧸ F) := by
    rw [Submodule.finrank_quotient, Module.finrank_fintype_fun_eq_card]
    omega
  let : Nonempty (Fin (finrank K ((P → K) ⧸ F))) := Fin.pos_iff_nonempty.mp hquot
  have hr := Submodule.finrank_le rect.toCoefficients.gamma.range
  rw [rect.finrank_range_gamma] at hr
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  have hc := G.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hc
  rw [hn] at hr
  nlinarith

/-- Внутренний бюджет δ+(q−1)h≤m из нормировки α(η⊗u)=1.
Формулировка без вычитания работает и при q=0; NZ и общность η не нужны. -/
theorem supportedTests_internal_budget [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (G : Set I) (η : Q → K) (u : P → K)
    (h1 : alg.toCoefficients.alpha (vecMulVec η u) = 1) :
    finrank K (alg.toCoefficients.supportedTests G) +
        Fintype.card Q * finrank K (alg.toCoefficients.supportedTestImage G) ≤
      G.ncard + finrank K (alg.toCoefficients.supportedTestImage G) := by
  classical
  let T := alg.toCoefficients.supportedTests G
  let H := alg.toCoefficients.supportedTestImage G
  let f : (G → K) →ₗ[K] Matrix Q S K := Fintype.linearCombination K (fun i : G ↦ alg.V i)
  let g : T →ₗ[K] (G → K) := LinearMap.pi
    (fun i ↦ (LinearMap.proj i.val).comp (alg.toCoefficients.gamma.domRestrict T))
  have hg : Function.Injective g := by
    intro C D he
    apply Subtype.ext
    apply alg.gamma_injective
    funext i
    by_cases hi : i ∈ G
    · exact congrFun he ⟨i, hi⟩
    · rw [(Coefficients.mem_supportedTests _ _ _).mp C.property i hi,
        (Coefficients.mem_supportedTests _ _ _).mp D.property i hi]
  let t : T →ₗ[K] H := ((Matrix.vecMulBilin K K u).domRestrict T).codRestrict H
    (fun C ↦ (le_iSup (fun D : T ↦ D.val.vecMulLinear.range) C) ⟨u, rfl⟩)
  let v : H →ₗ[K] Matrix Q S K := (vecMulVecBilin K K η).comp H.subtype
  have hfg : f.comp g = v.comp t := by
    ext C q s
    have he := alg.rotate.rotate.exact_formula C.val (vecMulVec η u)
    change vecMulVec η u * C.val = ∑ i,
      (alg.toCoefficients.gamma C.val i * alg.toCoefficients.alpha (vecMulVec η u) i) • alg.V i at he
    rw [h1] at he
    simp only [Pi.one_apply, mul_one] at he
    have hs : (∑ i, alg.toCoefficients.gamma C.val i • alg.V i) =
        ∑ i : G, alg.toCoefficients.gamma C.val i • alg.V i := by
      apply Finset.sum_congr_set G _ _ (fun _ _ ↦ rfl)
      intro i hi
      rw [(Coefficients.mem_supportedTests _ _ _).mp C.property i hi, zero_smul]
    rw [hs, vecMulVec_mul] at he
    exact congrFun (congrFun he.symm q) s
  have hr : finrank K (f.comp g).range ≤ finrank K H := by
    rw [hfg]
    rw [LinearMap.range_comp]
    exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_le t.range)
  have hb := finrank_range_add_le_of_injective f g hg
  have hmass := alg.supportedTestImage_mass G
  have hf : f.range = Submodule.span K (alg.V '' G) := by
    rw [Fintype.range_linearCombination]
    congr 1
    ext x
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨i.val, i.property, hi⟩,
      fun ⟨i, hi, he⟩ ↦ ⟨⟨i, hi⟩, he⟩⟩
  rw [hf, Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard] at hb
  dsimp only [T, H] at hb hr
  omega

/-- Нормировка на гиперплоскости автоматически предоставляет нужный простой вход. -/
theorem supportedTests_internal_budget_of_hyperplane [Nonempty Q]
    (alg : ExactAlgorithm K P Q S I) (G : Set I) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η)) :
    finrank K (alg.toCoefficients.supportedTests G) +
        Fintype.card Q * finrank K (alg.toCoefficients.supportedTestImage G) ≤
      G.ncard + finrank K (alg.toCoefficients.supportedTestImage G) := by
  obtain ⟨A, hA, he⟩ := h1
  obtain ⟨u, hu⟩ := hyperplaneInput_surjective η hη ⟨A, hA⟩
  apply alg.supportedTests_internal_budget G η u
  have hv := congrArg Subtype.val hu
  change vecMulVec η u = A at hv
  rwa [hv]

end MMRank.ExactAlgorithm
