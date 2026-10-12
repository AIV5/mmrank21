import MMRank.TraceSliceSpace
import MMRank.QuadraticThreeRay

/-! # Диагональный трёхмерный срез: три луча или одиночный канал
Простые срезы минимальной
трёхмерной оболочки дают линейную геометрию ядра; поле произвольно.
-/
noncomputable section
namespace MMRank
open Matrix Module
open scoped BigOperators
variable {K : Type*} [Field K]

/-- Диагональная матрица ранга≤1 лежит на одной координатной линии. -/
theorem diagonal_rank_le_one_single (A : Matrix (Fin 3) (Fin 3) K)
    (hr : A.rank ≤ 1) (hd : ∀ a b, a ≠ b → A a b = 0) :
    ∃ a : Fin 3, ∃ c : K, A = c • Matrix.single a a 1 := by
  classical
  have he : A = Matrix.diagonal (fun a ↦ A a a) := by
    ext a b
    by_cases hab : a = b
    · subst b; simp
    · simp [hd a b hab, hab]
  have hrD : (Matrix.diagonal (fun a ↦ A a a)).rank ≤ 1 := by rw [← he]; exact hr
  have hc : (Finset.univ.filter (fun a ↦ A a a ≠ 0)).card ≤ 1 := by
    simpa only [Matrix.rank_diagonal, Fintype.card_subtype] using hrD
  obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hc
  have hz (i : Fin 3) (hi : i ≠ a) : A i i = 0 := by
    by_contra hn
    exact hi (Finset.mem_singleton.mp (ha (by simp [hn])))
  refine ⟨a, A a a, he.trans ?_⟩
  rw [Matrix.smul_single, smul_eq_mul, mul_one, ← Matrix.diagonal_single]
  congr 1
  funext i
  by_cases hi : a = i
  · subst i; simp
  · simp [hi, hz i (Ne.symm hi)]

/-- Три формы задают координатный пучок плоскостей над произвольным полем. -/
def threeRayForms (π : (Fin 3 → K) →ₗ[K] (Fin 2 → K)) :
    Fin 3 → Dual K (Fin 3 → K) :=
  ![( (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) - LinearMap.proj 1).comp π,
    (LinearMap.proj 1).comp π, (LinearMap.proj 0).comp π]

def threeRayPlanes (π : (Fin 3 → K) →ₗ[K] (Fin 2 → K)) :
    Fin 3 → Submodule K (Fin 3 → K) := fun a => (threeRayForms π a).ker

/-- Разные плоскости пучка пересекаются ровно в ядре двумерного выхода. -/
theorem threeRayPlanes_inf_eq_ker (π : (Fin 3 → K) →ₗ[K] (Fin 2 → K))
    {a b : Fin 3} (hab : a ≠ b) : threeRayPlanes π a ⊓ threeRayPlanes π b = π.ker := by
  ext x
  simp only [Submodule.mem_inf, threeRayPlanes, LinearMap.mem_ker,
    funext_iff, Pi.zero_apply, Fin.forall_fin_two]
  fin_cases a <;> fin_cases b <;> try contradiction
  all_goals norm_num only [Fin.reduceFinMk, threeRayForms, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply] at *
  all_goals constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> simp_all

/-- Сюръективный двумерный выход даёт центр размерности1 и три плоскости2. -/
theorem threeRayPlanes_dimensions
    (π : (Fin 3 → K) →ₗ[K] (Fin 2 → K)) (hπ : Function.Surjective π) :
    finrank K π.ker = 1 ∧
    (∀ a, finrank K (threeRayPlanes π a) = 2) ∧
    Function.Injective (threeRayPlanes π) ∧
    ∀ a, π.ker ≤ threeRayPlanes π a := by
  have hc : finrank K π.ker = 1 := by
    have hh := π.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hπ, finrank_top] at hh
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hh
    omega
  have hn (a : Fin 3) : threeRayForms π a ≠ 0 := by
    fin_cases a
    · obtain ⟨x, hx⟩ := hπ ![1, 0]
      intro he
      have hh := DFunLike.congr_fun he x
      simp [threeRayForms, hx] at hh
    · obtain ⟨x, hx⟩ := hπ ![0, 1]
      intro he
      have hh := DFunLike.congr_fun he x
      simp [threeRayForms, hx] at hh
    · obtain ⟨x, hx⟩ := hπ ![1, 0]
      intro he
      have hh := DFunLike.congr_fun he x
      simp [threeRayForms, hx] at hh
  have hr (a : Fin 3) : finrank K (threeRayPlanes π a) = 2 := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero (hn a)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hh
    change finrank K (threeRayForms π a).ker = 2
    omega
  refine ⟨hc, hr, ?_, ?_⟩
  · intro a b he
    by_contra hab
    have hh := threeRayPlanes_inf_eq_ker π hab
    rw [he, inf_idem] at hh
    have hh' := congrArg (fun S : Submodule K (Fin 3 → K) => finrank K S) hh
    rw [hr b, hc] at hh'
    omega
  · intro a x hx
    change threeRayForms π a x = 0
    change π x = 0 at hx
    fin_cases a <;> simp [threeRayForms, hx]

/-- Трёхмерная оболочка rank1-семейства с единицей одновременно диагональна. -/
theorem exists_diagonalization_of_three_rank_one_span {I : Type*}
    (A : I → Matrix (Fin 3) (Fin 3) K)
    (hr : ∀ i, (A i).rank ≤ 1)
    (h1 : (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range A))
    (hd : finrank K (Submodule.span K (Set.range A)) = 3) :
    ∃ X Y : Matrix (Fin 3) (Fin 3) K, X * Y = 1 ∧ Y * X = 1 ∧
      ∀ B ∈ Submodule.span K (Set.range A), ∀ a b, a ≠ b → (Y * B * X) a b = 0 := by
  let M := Submodule.span K (Set.range A)
  have hs : Submodule.span K {B : M | B.val.rank ≤ 1} = ⊤ :=
    span_rank_one_subtype_eq_top_of_spanning_family A hr
  let b₀ : Basis (Fin 3) K M := (Module.finBasis K M).reindex (finCongr hd)
  obtain ⟨b, hb⟩ := exists_basis_in_spanning_set b₀ {B : M | B.val.rank ≤ 1} hs
  exact rank_one_identity_basis_diagonalization M b hb h1

/-- Выходная диагональная координата после смены базиса. -/
def conjugateDiagonalForm (X Y : Matrix (Fin 3) (Fin 3) K) (a : Fin 3) :
    Dual K (Matrix (Fin 3) (Fin 3) K) :=
  (Matrix.entryLinearMap K K a a).comp
    ((mulRightLinearMap (Fin 3) K X).comp (mulLeftLinearMap (Fin 3) K Y))

/-- Разности диагоналей дают естественный двумерный выход пучка. -/
def diagonalSliceProjection (X Y : Matrix (Fin 3) (Fin 3) K)
    (Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K) :
    (Fin 3 → K) →ₗ[K] (Fin 2 → K) :=
  LinearMap.pi ![(conjugateDiagonalForm X Y 1 - conjugateDiagonalForm X Y 0).comp Z,
    (conjugateDiagonalForm X Y 2 - conjugateDiagonalForm X Y 0).comp Z]

/-- Проекция по скалярной единице имеет ровно ядро Z; это исключает
скрытую дополнительную прямую в определении центра. -/
theorem diagonalSliceProjection_ker
    (X Y : Matrix (Fin 3) (Fin 3) K) (hXY : X * Y = 1)
    (Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hz : ∀ x, Z x 0 0 = 0)
    (hd : ∀ x a b, a ≠ b → (Y * Z x * X) a b = 0) :
    (diagonalSliceProjection X Y Z).ker = Z.ker := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    have hh0 := congrFun hx 0
    have hh1 := congrFun hx 1
    change (Y * Z x * X) 1 1 - (Y * Z x * X) 0 0 = 0 at hh0
    change (Y * Z x * X) 2 2 - (Y * Z x * X) 0 0 = 0 at hh1
    have hsc : Y * Z x * X = (Y * Z x * X) 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
      ext a b
      by_cases hab : a = b
      · subst b
        fin_cases a <;> simp_all [sub_eq_zero]
      · simp [hd x a b hab, hab]
    have hZ : Z x = (Y * Z x * X) 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
      calc
        Z x = (X * Y) * Z x * (X * Y) := by simp only [hXY, Matrix.one_mul, Matrix.mul_one]
        _ = X * (Y * Z x * X) * Y := by simp only [Matrix.mul_assoc]
        _ = _ := (congrArg (fun B ↦ X * B * Y) hsc).trans
          (by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hXY])
    have hscalar := congrArg (fun B : Matrix (Fin 3) (Fin 3) K => B 0 0) hZ
    have hzero : (Y * Z x * X) 0 0 = 0 := by simpa [hz x] using hscalar.symm
    simpa [hzero] using hZ
  · intro hx
    ext a
    fin_cases a <;> simp [diagonalSliceProjection, conjugateDiagonalForm, hx]

/-- При ранге Z=2 проекция сюръективна на две координаты. -/
theorem diagonalSliceProjection_surjective
    (X Y : Matrix (Fin 3) (Fin 3) K) (hXY : X * Y = 1)
    (Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hz : ∀ x, Z x 0 0 = 0)
    (hd : ∀ x a b, a ≠ b → (Y * Z x * X) a b = 0)
    (hr : finrank K Z.range = 2) : Function.Surjective (diagonalSliceProjection X Y Z) := by
  have hk := diagonalSliceProjection_ker X Y hXY Z hz hd
  have hZ := Z.finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hr] at hZ
  have hπ := (diagonalSliceProjection X Y Z).finrank_range_add_finrank_ker
  rw [hk] at hπ
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hπ
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

/-- Реконструкция по трём внешним классам: каждый класс либо имеет два
индекса, либо его единственный индекс одновременно является выходным и
квадратично отделимым каналом. -/
theorem three_ray_output_dichotomy {L I : Type*} [AddCommGroup L] [Module K L]
    [Fintype I] [DecidableEq I]
    (w : I → L) (t : L) (ht : t ≠ 0) (μ : I → Fin 3 → K)
    (π : (Fin 3 → K) →ₗ[K] (Fin 2 → K)) (hπ : Function.Surjective π)
    (η : Fin 3 → I → K)
    (hrec : ∀ a, ∑ i, η a i • w i = t)
    (hsupp : ∀ a i, η a i ≠ 0 → μ i ∈ threeRayPlanes π a ∧ μ i ∉ π.ker)
    (hcover : ∀ i, ∃ a, μ i ∈ threeRayPlanes π a) :
    (∃ C : Submodule K (Fin 3 → K), ∃ H : ThreeRayCover μ Finset.univ C,
      ∀ a, t ∈ Submodule.span K (w '' {i | μ i ∈ H.ray a ∧ μ i ∉ C})) ∨
    ∃ i, t ∈ Submodule.span K {w i} ∧
      i ∈ separatedIndices (K := K) (fun j => quadraticVeronese (μ j)) := by
  classical
  obtain ⟨hc, hr, hinj, hle⟩ := threeRayPlanes_dimensions π hπ
  let J : Fin 3 → Finset I := fun a => Finset.univ.filter
    fun i => μ i ∈ threeRayPlanes π a ∧ μ i ∉ π.ker
  have hout (a) : t ∈ Submodule.span K (w '' {i | μ i ∈ threeRayPlanes π a ∧ μ i ∉ π.ker}) := by
    rw [← hrec a]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : η a i = 0
    · simp [hi]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hsupp a i hi, rfl⟩)
  by_cases hall : ∀ a, 2 ≤ (J a).card
  · left
    let H : ThreeRayCover μ Finset.univ π.ker :=
          { finrank_center := hc
            ray := threeRayPlanes π
            finrank_ray := hr
            ray_injective := hinj
            center_le_ray := hle
            cover := fun i _ => hcover i
            active := hall }
    exact ⟨π.ker, H, hout⟩
  · right
    obtain ⟨a, ha⟩ : ∃ a, (J a).card ≤ 1 := by
      push Not at hall
      obtain ⟨a, ha⟩ := hall
      exact ⟨a, by omega⟩
    obtain ⟨i, hi⟩ : ∃ i, η a i ≠ 0 := by
      by_contra! hn
      have hh := hrec a
      simp [hn] at hh
      exact ht hh.symm
    have hiJ : i ∈ J a := by simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]; exact hsupp a i hi
    have hunique (j) (hj : j ∈ J a) : j = i := (Finset.card_le_one.mp ha) j hj i hiJ
    have hsub : w '' {j | μ j ∈ threeRayPlanes π a ∧ μ j ∉ π.ker} ⊆ {w i} := by
      rintro _ ⟨j, hj, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (congrArg w (hunique j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)))
    have htspan : t ∈ Submodule.span K {w i} := Submodule.span_mono hsub (hout a)
    let b : Fin 3 := a + 1
    let c : Fin 3 := a + 2
    have hab : a ≠ b := by fin_cases a <;> decide
    have hac : a ≠ c := by fin_cases a <;> decide
    have hni (r : Fin 3) (har : a ≠ r) : threeRayForms π r (μ i) ≠ 0 := by
      intro hz
      apply (hsupp a i hi).2
      rw [← threeRayPlanes_inf_eq_ker π har, Submodule.mem_inf]
      exact ⟨(hsupp a i hi).1, hz⟩
    obtain ⟨ell, hell⟩ := exists_quadratic_product_form (threeRayForms π b) (threeRayForms π c)
    refine ⟨i, htspan, (mem_separatedIndices (K := K) _ i).mpr ⟨ell, ?_, ?_⟩⟩
    · rw [hell]
      exact mul_ne_zero (hni b hab) (hni c hac)
    · intro j hji
      rw [hell]
      obtain ⟨r, hjr⟩ := hcover j
      by_cases hra : r = a
      · subst r
        have hjC : μ j ∈ π.ker := by
          by_contra hn
          exact hji (hunique j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hjr, hn⟩⟩))
        have hb0 : threeRayForms π b (μ j) = 0 := hle b hjC
        simp [hb0]
      · have hrc : r = b ∨ r = c := by
          fin_cases a <;> fin_cases r <;> simp_all [b, c]
        rcases hrc with rfl | rfl
        · change threeRayForms π b (μ j) = 0 at hjr
          simp [hjr]
        · change threeRayForms π c (μ j) = 0 at hjr
          simp [hjr]

/-- Скалярная единица исчезает из разностей диагоналей. -/
theorem diagonalSliceProjection_affine
    (X Y : Matrix (Fin 3) (Fin 3) K) (hYX : Y * X = 1)
    (Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (x : Fin 3 → K) (c : K) (A : Matrix (Fin 3) (Fin 3) K)
    (ha : A = c • 1 + Z x) :
    diagonalSliceProjection X Y Z x =
      ![(Y * A * X) 1 1 - (Y * A * X) 0 0,
        (Y * A * X) 2 2 - (Y * A * X) 0 0] := by
  ext a
  fin_cases a <;>
    simp [diagonalSliceProjection, conjugateDiagonalForm, ha,
      Matrix.mul_add, Matrix.add_mul, hYX]

/-- Полный контракт трёхмерного среза: три активных луча с тремя независимыми
выходными представлениями либо один отделимый выходный канал. -/
theorem diagonal_three_slice_dichotomy {L I : Type*} [AddCommGroup L] [Module K L]
    [Fintype I] [DecidableEq I]
    (w : I → L) (t : L) (ht : t ≠ 0) (μ : I → Fin 3 → K)
    (hμ : Submodule.span K (Set.range μ) = ⊤)
    (Z : (Fin 3 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hz : ∀ x, Z x 0 0 = 0) (hrZ : finrank K Z.range = 2)
    (c : I → K) (A : I → Matrix (Fin 3) (Fin 3) K)
    (ha : ∀ i, A i = c i • 1 + Z (μ i)) (hr : ∀ i, (A i).rank ≤ 1)
    (h1 : (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range A))
    (hd : finrank K (Submodule.span K (Set.range A)) = 3)
    (hrec : ∀ χ : Dual K (Matrix (Fin 3) (Fin 3) K),
      ∑ i, χ (A i) • w i = χ 1 • t) :
    (∃ C : Submodule K (Fin 3 → K), ∃ H : ThreeRayCover μ Finset.univ C,
      ∀ a, t ∈ Submodule.span K (w '' {i | μ i ∈ H.ray a ∧ μ i ∉ C})) ∨
    ∃ i, t ∈ Submodule.span K {w i} ∧
      i ∈ separatedIndices (K := K) (fun j => quadraticVeronese (μ j)) := by
  obtain ⟨X, Y, hXY, hYX, hdiag⟩ :=
    exists_diagonalization_of_three_rank_one_span A hr h1 hd
  let M := Submodule.span K (Set.range A)
  have hZM : Z.range ≤ M := by
    change Z.range ≤ Submodule.span K (Set.range A)
    rw [span_trace_slice_eq_one_sup_range A c μ hμ Z ha h1]
    exact le_sup_right
  have hDZ (x a b) (hab : a ≠ b) : (Y * Z x * X) a b = 0 :=
    hdiag _ (hZM ⟨x, rfl⟩) a b hab
  let π := diagonalSliceProjection X Y Z
  have hπ : Function.Surjective π := diagonalSliceProjection_surjective X Y hXY Z hz hDZ hrZ
  let η : Fin 3 → I → K := fun a i => conjugateDiagonalForm X Y a (A i)
  have hη (a) : ∑ i, η a i • w i = t := by
    simpa [η, conjugateDiagonalForm, hYX] using hrec (conjugateDiagonalForm X Y a)
  have hB (i) : (Y * A i * X).rank ≤ 1 :=
    ((Matrix.rank_mul_le_left (Y * A i) X).trans (Matrix.rank_mul_le_right Y (A i))).trans (hr i)
  have hdi (i a b) (hab : a ≠ b) : (Y * A i * X) a b = 0 :=
    hdiag _ (Submodule.subset_span (Set.mem_range_self i)) a b hab
  have hproj (i) : π (μ i) =
      ![(Y * A i * X) 1 1 - (Y * A i * X) 0 0,
        (Y * A i * X) 2 2 - (Y * A i * X) 0 0] :=
    diagonalSliceProjection_affine X Y hYX Z (μ i) (c i) (A i) (ha i)
  have hcover (i) : ∃ a, μ i ∈ threeRayPlanes π a := by
    obtain ⟨a, s, hs⟩ := diagonal_rank_le_one_single _ (hB i) (hdi i)
    refine ⟨a, ?_⟩
    change threeRayForms π a (μ i) = 0
    fin_cases a <;> simp [threeRayForms, hproj, hs]
  have hsupp (a i) (hi : η a i ≠ 0) : μ i ∈ threeRayPlanes π a ∧ μ i ∉ π.ker := by
    obtain ⟨r, s, hs⟩ := diagonal_rank_le_one_single _ (hB i) (hdi i)
    have hra : r = a := by
      by_contra hn
      apply hi
      change (Y * A i * X) a a = 0
      rw [hs]
      simp [hn]
    subst r
    have hsn : s ≠ 0 := by
      intro hn
      apply hi
      change (Y * A i * X) a a = 0
      simp [hs, hn]
    constructor
    · change threeRayForms π a (μ i) = 0
      fin_cases a <;> simp [threeRayForms, hproj, hs]
    · change π (μ i) ≠ 0
      rw [hproj, hs]
      fin_cases a <;> simp [funext_iff, Fin.forall_fin_two, hsn]
  exact three_ray_output_dichotomy w t ht μ π hπ η hη hsupp hcover

end MMRank
