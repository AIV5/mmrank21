module

public import MMRank.ThreeRayGeometry
public import MMRank.DisjointOutputKernelBudget

@[expose] public section

/-! # Один центр задаёт не более одного направления выхода

Независимость координатных носителей и размерностная оценка
образов с непересекающимися носителями ограничивают число направлений выхода.
-/
namespace MMRank
open Module Submodule
open scoped BigOperators Classical

variable {K I : Type*} [Field K]

/-- Координатные векторы, равные нулю вне данного множества индексов. -/
def supportedCoordinates (s : Set I) : Submodule K (I → K) :=
  Submodule.pi sᶜ (fun _ ↦ ⊥)

@[simp] theorem mem_supportedCoordinates {s : Set I} {x : I → K} :
    x ∈ supportedCoordinates (K := K) s ↔ ∀ i, i ∉ s → x i = 0 := by
  simp [supportedCoordinates, Submodule.mem_pi]

/-- Непересекающиеся множества координат задают независимые подпространства. -/
theorem supportedCoordinates_iSupIndep {J : Type*} (s : J → Set I)
    (hs : Pairwise fun a b ↦ Disjoint (s a) (s b)) :
    iSupIndep (fun a ↦ supportedCoordinates (K := K) (s a)) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro t v hv hzero a ha
  ext i
  by_cases hi : i ∈ s a
  · have hb (b : J) (hb : b ∈ t) (hba : b ≠ a) : v b i = 0 := by
      apply (mem_supportedCoordinates.mp (hv b hb)) i
      exact fun hbi ↦ Set.disjoint_left.mp (hs hba) hbi hi
    have he : (∑ b ∈ t, v b i) = 0 := by
      simpa only [Finset.sum_apply, Pi.zero_apply] using congr_fun hzero i
    rw [Finset.sum_eq_single_of_mem a ha hb] at he
    exact he
  · exact (mem_supportedCoordinates.mp (hv a ha)) i hi

/-- В конечном координатном пространстве поддержанный вектор является
линейной комбинацией стандартных векторов тех же индексов. -/
theorem supportedCoordinates_eq_span [Fintype I] [DecidableEq I] (s : Set I) :
    supportedCoordinates (K := K) s =
      Submodule.span K ((fun i : I ↦ Pi.single i (1 : K)) '' s) := by
  classical
  ext x
  simpa only [Pi.spanSubset, Pi.basisFun_apply] using
    (mem_supportedCoordinates (K := K) (s := s) (x := x)).trans
      (Pi.mem_spanSubset_iff (R := K) (s := s) (v := x)).symm

section ThreeRay
variable {E L : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup L] [Module K L] [FiniteDimensional K L] [Fintype I]
  {μ : I → E} {s : Finset I} {C : Submodule K E}

/-- Индексы на луче, не лежащие на самом центре. -/
def ThreeRayCover.activeIndices (H : ThreeRayCover μ s C) (a : Fin 3) : Set I :=
  {i | i ∈ s ∧ μ i ∈ H.ray a ∧ μ i ∉ C}

/-- Координатное пространство одного активного класса. -/
def ThreeRayCover.activeCoordinateSpace (H : ThreeRayCover μ s C) (a : Fin 3) :
    Submodule K (I → K) := supportedCoordinates (H.activeIndices a)

/-- Выходы, вычислимые на одном активном классе. -/
def ThreeRayCover.activeOutput (H : ThreeRayCover μ s C) (F : (I → K) →ₗ[K] L)
    (a : Fin 3) : Submodule K L := (H.activeCoordinateSpace a).map F

omit [FiniteDimensional K E] [FiniteDimensional K L] in
/-- Выход класса есть оболочка соответствующих отдельных выходных матриц. -/
theorem ThreeRayCover.activeOutput_eq_span [DecidableEq I]
    (H : ThreeRayCover μ s C) (F : (I → K) →ₗ[K] L) (a : Fin 3) :
    H.activeOutput F a = Submodule.span K
      ((fun i ↦ F (Pi.single i 1)) '' H.activeIndices a) := by
  unfold ThreeRayCover.activeOutput ThreeRayCover.activeCoordinateSpace
  rw [supportedCoordinates_eq_span, Submodule.map_span, Set.image_image]

omit [Fintype I] in
/-- Три активных класса одного центра независимы в координатном пространстве. -/
theorem ThreeRayCover.activeCoordinateSpace_iSupIndep
    (H : ThreeRayCover μ s C) (hE : finrank K E = 3) :
    iSupIndep H.activeCoordinateSpace := by
  apply supportedCoordinates_iSupIndep
  intro a b hab
  apply Set.disjoint_left.mpr
  intro i hi hj
  exact hab (H.active_ray_unique hE hi.2.1 hj.2.1 hi.2.2)

/-- Три независимых представления оставляют общему выходу размерность≤1,
если ядро реконструкции имеет размерность≤3. -/
theorem ThreeRayCover.activeOutput_intersection_finrank_le_one
    (H : ThreeRayCover μ s C) (hE : finrank K E = 3)
    (F : (I → K) →ₗ[K] L) (hker : finrank K F.ker ≤ 3) :
    finrank K (⨅ a, H.activeOutput F a : Submodule K L) ≤ 1 := by
  let B : Submodule K L := ⨅ a, H.activeOutput F a
  have hb := disjoint_output_span_kernel_budget F H.activeCoordinateSpace
    (H.activeCoordinateSpace_iSupIndep hE) B (fun a ↦ iInf_le _ a)
  simp only [Fintype.card_fin] at hb
  change finrank K B ≤ 1
  omega

omit [Fintype I] in
/-- Один активный индекс восстанавливает луч среди лучей другого
сертификата того же центра. Перестановку лучей строить не нужно. -/
theorem ThreeRayCover.exists_matching_ray
    (H G : ThreeRayCover μ s C) (hE : finrank K E = 3) (a : Fin 3) :
    ∃ b, H.ray a = G.ray b := by
  have hn := H.active a
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega :
    0 < (s.filter fun i ↦ μ i ∈ H.ray a ∧ μ i ∉ C).card)
  obtain ⟨his, hia, hiC⟩ := Finset.mem_filter.mp hi
  obtain ⟨b, hib⟩ := G.cover i his
  refine ⟨b, ?_⟩
  by_contra hne
  have he := H.inf_plane_eq_center hE (G.ray b) (G.finrank_ray b)
    (G.center_le_ray b) a hne
  exact hiC (he ▸ (show μ i ∈ H.ray a ⊓ G.ray b from ⟨hia, hib⟩))

/-- Два выхода, представимые на всех трёх классах одного и того же центра,
не могут быть линейно независимы. -/
theorem ThreeRayCover.not_linearIndependent_outputs_of_same_center
    (H G : ThreeRayCover μ s C) (hE : finrank K E = 3)
    (F : (I → K) →ₗ[K] L) (hker : finrank K F.ker ≤ 3) (t u : L)
    (ht : ∀ a, t ∈ H.activeOutput F a) (hu : ∀ a, u ∈ G.activeOutput F a) :
    ¬ LinearIndependent K ![t, u] := by
  intro hli
  let B : Submodule K L := ⨅ a, H.activeOutput F a
  have htB : t ∈ B := (Submodule.mem_iInf _).mpr ht
  have huB : u ∈ B := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    obtain ⟨b, hab⟩ := H.exists_matching_ray G hE a
    have he : H.activeOutput F a = G.activeOutput F b := by
      simp only [ThreeRayCover.activeOutput, ThreeRayCover.activeCoordinateSpace,
        ThreeRayCover.activeIndices, hab]
    rw [he]
    exact hu b
  have hsub : Submodule.span K (Set.range (![t, u] : Fin 2 → L)) ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    fin_cases a <;> assumption
  have hdim := finrank_span_eq_card hli
  simp only [Fintype.card_fin] at hdim
  have hm := Submodule.finrank_mono hsub
  have hbound := H.activeOutput_intersection_finrank_le_one hE F hker
  change finrank K B ≤ 1 at hbound
  omega

end ThreeRay
end MMRank
