import MMRank.SecondConductorIntoFamily
import MMRank.GenericHyperplane
import MMRank.RestrictedTwoConductorBound

/-! # Полная размерность произведения третьих слов на второй кондуктор

Согласованные базисы простых тестов делают диагональные факторы второго
кондуктора инъективными. Точность алгоритма тогда отражает любое соотношение
между γ(Cₐ)zₐ в нулевые координаты всех Cₐ. Это заменяет анализ носителей
одной оценкой размерности над произвольным полем.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
open scoped BigOperators
variable {K P Q S I T J : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I] [Fintype T]

/-- Сумма произведений третьих коэффициентных слов на фиксированные слова. -/
noncomputable def gammaWordSum (alg : ExactAlgorithm K P Q S I) (z : T → I → K) :
    (T → Matrix P S K) →ₗ[K] (I → K) where
  toFun C := ∑ a, alg.toCoefficients.gamma (C a) * z a
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum]

/-- Линейно независимые элементы Z остаются независимыми с произвольными
матричными коэффициентами γ(C). Нужна полная точность, а не только NZ. -/
theorem gammaWordSum_injective_of_diagonal_secondConductor
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ v ∈ alg.toCoefficients.betaInto (coordinateHyperplane η), a * v = 0 → a = 0 ∨ v = 0)
    (b : Basis J K (P → K)) (c : Basis J K (S → K))
    (ht : ∀ j, alg.toCoefficients.gamma (rowLinearEquiv.symm ((b.coord j).smulRight (c j))) ∈
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (z : T → conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
      (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (hz : LinearIndependent K z) :
    Function.Injective (alg.gammaWordSum (fun a ↦ (z a).val)) := by
  classical
  let F := coordinateHyperplane η
  let B := alg.secondConductorIntoFamily η
  have ht' j := alg.test_mem_jointSymmetrizer_into η hη h1 _ (ht j)
  have hn := alg.secondConductorIntoFamily_nz η hη h1 hnz
  apply (injective_iff_map_eq_zero _).mpr
  intro C hC
  change ∑ a, alg.toCoefficients.gamma (C a) * (z a).val = 0 at hC
  have hcoord (j : J) (u : P → K) (a : T) : c.coord j ((C a).vecMulLinear u) = 0 := by
    let Bj (a : T) := rowLinearEquiv.symm (F.subtype.comp (B (z a) (b j)))
    have hbeta (a : T) : alg.toCoefficients.beta (Bj a) =
        alg.toCoefficients.alpha (hyperplaneInput η (b j)).val * (z a).val :=
      alg.betaOnLinearInto_secondConductor η (z a) (b j)
    have hp : ∑ a, C a * Bj a = 0 := by
      apply alg.sum_mul_eq_zero_of_sum_beta_mul_gamma_eq_zero
      simp_rw [hbeta, mul_assoc, mul_comm ((z _).val)]
      rw [← Finset.mul_sum, hC, mul_zero]
    have hBj (a : T) : (Bj a).vecMulLinear = F.subtype.comp (B (z a) (b j)) := by
      rw [← rowLinearEquiv_apply, rowLinearEquiv.apply_symm_apply]
    have hh : ∑ a, B (z a) (b j) ((C a).vecMulLinear u) = 0 := by
      apply Subtype.ext
      have hh := congrArg (fun D : Matrix P Q K ↦ rowLinearEquiv D u) hp
      simpa only [map_sum, map_zero, LinearMap.sum_apply, LinearMap.zero_apply,
        rowLinearEquiv_apply, rowLinear_mul, hBj, LinearMap.comp_apply,
        Submodule.coe_sum, Submodule.coe_zero, Submodule.subtype_apply] using hh
    have hi := basisDiagonalFactor_injective B b c ht' hn j
    have hzj := hz.map' (basisDiagonalFactor B b c j) (LinearMap.ker_eq_bot.mpr hi)
    apply Fintype.linearIndependent_iff.mp hzj (fun a ↦ c.coord j ((C a).vecMulLinear u)) ?_ a
    simpa only [diagonalFamily_basis_eq_smulRight B b c ht', LinearMap.smulRight_apply,
      Function.comp_apply] using hh
  funext a
  apply rowLinearEquiv.injective
  apply LinearMap.ext
  intro u
  apply c.ext_elem
  intro j
  simpa [Basis.coord_apply] using hcoord j u a

omit [Fintype T] in
/-- Диагональные тесты дают нижнюю оценку длины p s dim Z + dim A_F.
Ни dim Z=dim F, ни алгебраическая замкнутость, ни атомы не предполагаются.
Два базиса с одним индексным множеством, в частности, требуют |P|=|S|. -/
theorem length_bound_of_diagonal_secondConductor
    [Nonempty P] [Nonempty Q] [Nonempty S]
    (alg : ExactAlgorithm K P Q S I) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ v ∈ alg.toCoefficients.betaInto (coordinateHyperplane η), a * v = 0 → a = 0 ∨ v = 0)
    (b : Basis J K (P → K)) (c : Basis J K (S → K))
    (ht : ∀ j, alg.toCoefficients.gamma (rowLinearEquiv.symm ((b.coord j).smulRight (c j))) ∈
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η))) :
    Fintype.card P * Fintype.card S *
      finrank K (conductor (alg.toCoefficients.betaInto (coordinateHyperplane η))
        (alg.toCoefficients.alphaOn (coordinateHyperplane η))) + Fintype.card P ≤ Fintype.card I := by
  classical
  let F := coordinateHyperplane η
  let M := alg.toCoefficients.alphaOn F
  let Z := conductor (alg.toCoefficients.betaInto F) M
  let z := Module.finBasis K Z
  let L := alg.gammaWordSum (fun a ↦ (z a).val)
  have hi : Function.Injective L :=
    alg.gammaWordSum_injective_of_diagonal_secondConductor η hη h1 hnz b c ht z z.linearIndependent
  have hr : L.range ≤ coordinateOrthogonal M := by
    rintro _ ⟨C, rfl⟩
    change ∑ a, alg.toCoefficients.gamma (C a) * (z a).val ∈ coordinateOrthogonal M
    apply Submodule.sum_mem
    intro a _
    apply Submodule.mem_orthogonalBilin.mpr
    intro m hm
    have hzB := conductor_le_of_one_mem (alg.toCoefficients.betaInto F) M h1 (z a).property
    have hh := alg.restricted_triple_sum_eq_zero F hm hzB ⟨C a, rfl⟩
    simpa [dotProductBilin, dotProduct, mul_assoc, mul_comm, mul_left_comm] using hh
  have hd := Submodule.finrank_mono hr
  rw [LinearMap.finrank_range_of_inj hi, finrank_coordinateOrthogonal] at hd
  have hM : finrank K M = Fintype.card P := by
    have hF := finrank_coordinateHyperplane_add_one η hη
    dsimp [M, F]
    rw [alg.finrank_alphaOn]
    have he : Fintype.card Q - finrank K (coordinateHyperplane η) = 1 := by omega
    rw [he, mul_one]
  have hdom : finrank K (Fin (finrank K Z) → Matrix P S K) =
      Fintype.card P * Fintype.card S * finrank K Z := by
    simp [Module.finrank_pi_fintype, Module.finrank_matrix, mul_comm]
  rw [hdom, hM] at hd
  have hm := M.finrank_le
  rw [Module.finrank_pi, hM] at hm
  change Fintype.card P * Fintype.card S * finrank K Z + Fintype.card P ≤ Fintype.card I
  omega

omit [Fintype T] in
/-- Малый первый кондуктор и согласованные диагональные тесты уже дают21.
Поле произвольно; нулевой рост,
атомы, нормированный пакет и точное равенство dim Z=2 не предполагаются.
Достаточны общая нижняя на dim D+dim Z и оценка произведения γ·Z. -/
theorem length_ge_twenty_one_of_small_diagonal_conductor
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (hnz : ∀ a ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η),
      ∀ v ∈ alg.toCoefficients.betaInto (coordinateHyperplane η), a * v = 0 → a = 0 ∨ v = 0)
    (b : Basis J K (P → K)) (c : Basis J K (S → K))
    (ht : ∀ j, alg.toCoefficients.gamma (rowLinearEquiv.symm ((b.coord j).smulRight (c j))) ∈
      conductor alg.toCoefficients.gamma.range (alg.toCoefficients.alphaOn (coordinateHyperplane η)))
    (hd : finrank K (conductor alg.toCoefficients.gamma.range
      (alg.toCoefficients.alphaOn (coordinateHyperplane η))) ≤ 3) :
    21 ≤ Fintype.card I := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty S := Fintype.card_pos_iff.mp (by omega)
  have hF := finrank_coordinateHyperplane_add_one η hη
  have hsum := alg.restricted_two_conductor_dimension_sum_bound
    (coordinateHyperplane η) 1 (by omega) (by omega) h1 (by simp [hp])
  have hprod := alg.length_bound_of_diagonal_secondConductor η hη h1 hnz b c ht
  simp only [hp, hq, hs] at hsum hprod
  omega

end MMRank.ExactAlgorithm
