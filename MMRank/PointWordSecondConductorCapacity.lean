module

public import MMRank.PointWordPhysical
public import MMRank.LowRankConductor

@[expose] public section

/-! # Вместимость второго кондуктора при одном точечном слове

Ядро одной активной координаты M имеет коразмерность один. Его произведение
на Z поднимается в отображения S/im C→F: общий образ остальных значений
первого кондуктора и классификация их рангов не нужны. Поле произвольно.
-/

namespace MMRank.ExactAlgorithm
open Module Matrix

variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  [Nonempty P] [Nonempty Q] [Nonempty S]

omit [Nonempty S] in
/-- Один точечный физический тест даёт усиленный бюджет dim M+dim Z:
достаточно ненулевого Z и dim M≥2; F и размеры произвольны. -/
theorem pointWord_secondConductor_capacity
    (alg : ExactAlgorithm K P Q S I) (F : Submodule K (Q → K))
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn F)
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn F, ∀ b ∈ alg.toCoefficients.betaInto F,
      a * b = 0 → a = 0 ∨ b = 0)
    (C : Matrix P S K)
    (hp : IsPointWord (alg.toCoefficients.alphaOn F) (alg.toCoefficients.gamma C))
    (hM : 2 ≤ finrank K (alg.toCoefficients.alphaOn F))
    (hZ : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F) ≠ ⊥) :
    finrank K (alg.toCoefficients.alphaOn F) +
      finrank K (conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F)) ≤
      (Fintype.card S - C.rank) * finrank K F + 2 := by
  obtain ⟨i, hi⟩ : ∃ i, alg.toCoefficients.gamma C i ≠ 0 := by
    simpa [funext_iff] using hp.1
  let M := alg.toCoefficients.alphaOn F
  let H := (coordinateEval M i).ker.map M.subtype
  change 2 ≤ finrank K M at hM
  have he : coordinateEval M i ≠ 0 := (coordinateEval_ne_zero_iff M i).mpr
    ⟨1, h1, by simp⟩
  have hdim : finrank K H + 1 = finrank K M := by
    rw [Submodule.finrank_map_subtype_eq]
    exact Module.Dual.finrank_ker_add_one_of_ne_zero he
  have hH : H ≠ ⊥ := by
    intro hh
    rw [hh, finrank_bot] at hdim
    omega
  have hHM : H ≤ M := by
    rintro _ ⟨a, _, rfl⟩
    exact a.property
  obtain ⟨A₀, hA₀, hα₀⟩ := (show (1 : I → K) ∈ M from h1)
  let d : conductor alg.toCoefficients.gamma.range M :=
    ⟨alg.toCoefficients.gamma C, hp.mem_conductor ⟨C, rfl⟩⟩
  have hC₀ : alg.conductorMatrix F d ⟨A₀, hA₀⟩ = C := by
    rw [alg.conductorMatrix_eq_smul_of_pointWord F C hp i hi]
    rw [hα₀]
    simp
  have hkill : ∀ A : matricesKilling (P := P) F,
      alg.toCoefficients.alpha A.val ∈ H → ∀ z,
      C.vecMulLinear.range ≤ (alg.secondConductorMatrix F z A).val.vecMulLinear.ker := by
    intro A hA z
    obtain ⟨a, ha, hea⟩ := hA
    have hai : alg.toCoefficients.alpha A.val i = 0 := by
      rw [← hea]
      change a.val i = 0
      exact ha
    have hz : alg.conductorMatrix F d A = 0 := by
      rw [alg.conductorMatrix_eq_smul_of_pointWord F C hp i hi, hai, zero_smul]
    apply LinearMap.range_le_ker_iff.mpr
    rw [← rowLinear_mul, ← hC₀, alg.two_conductor_annihilation F d z A ⟨A₀, hA₀⟩ hz]
    simpa only [rowLinearEquiv_apply] using
      map_zero (rowLinearEquiv (K := K) (Q := P) (P := Q))
  have hu := alg.second_product_capacity_of_subspace F H hHM C.vecMulLinear.range hkill
  rw [← matrix_rank_eq_finrank_rowRange] at hu
  have hl := coordinate_product_growth_of_noZeroDivisors H _ hH hZ
    (fun a ha b hb ↦ hnz a (hHM ha) b (conductor_le_of_one_mem _ _ h1 hb))
  change finrank K M + _ ≤ _
  omega

/-- В формате s=3, dim F=2 и dim M≥3 одного точечного слова уже достаточно
для z≤3. Отдельные ранги всего первого семейства не рассматриваются. -/
theorem secondConductor_finrank_le_three_of_point_word_direct
    (alg : ExactAlgorithm K P Q S I) (F : Submodule K (Q → K))
    (hs : Fintype.card S = 3) (hF : finrank K F = 2)
    (hsize : 3 ≤ Fintype.card P * (Fintype.card Q - finrank K F))
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn F)
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn F, ∀ b ∈ alg.toCoefficients.betaInto F,
      a * b = 0 → a = 0 ∨ b = 0)
    (d : conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn F))
    (hp : IsPointWord (alg.toCoefficients.alphaOn F) d.val) :
    finrank K (conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F)) ≤ 3 := by
  by_cases hZ : conductor (alg.toCoefficients.betaInto F) (alg.toCoefficients.alphaOn F) = ⊥
  · rw [hZ, finrank_bot]
    omega
  obtain ⟨C, hC⟩ := conductor_le_of_one_mem _ _ h1 d.property
  have hpC : IsPointWord (alg.toCoefficients.alphaOn F) (alg.toCoefficients.gamma C) := by
    rwa [hC]
  have hC0 : C ≠ 0 := by intro hh; rw [hh, map_zero] at hpC; exact hpC.1 rfl
  have hr : 1 ≤ C.rank := by
    have := mt (matrix_rank_eq_zero_iff C).mp hC0
    omega
  have hm := alg.finrank_alphaOn F
  have hh := alg.pointWord_secondConductor_capacity F h1 hnz C hpC (by omega) hZ
  rw [hs, hF] at hh
  omega

end MMRank.ExactAlgorithm
