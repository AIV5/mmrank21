import MMRank.JointSymmetrizers
import MMRank.RankOneMatrixSpaces
import MMRank.RestrictedInputs
import MMRank.NonsingularBilinear

/-! # Малые совместные симметризаторы семейства без делителей нуля

Структурный контракт: большое пространство параметров Z исключает
сингулярные симметризаторы ранга≥2. Если симметризаторы имеют общий
образный фактор, большой полный образ B исключает этот фактор; если
они имеют общий входной фактор, его исключает вместимость Z.

Размеры произвольны; замкнутость поля используется только для квадратного
семейства инъективных отображений. -/

namespace MMRank
open Module Matrix

section Abstract
variable {K U S F Z : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup Z] [Module K Z]

omit [FiniteDimensional K U] in
/-- Ядро одного симметризатора ограничивает Z отображениями S/im C→F. -/
theorem jointSymmetrizer_capacity_of_kernel
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] F)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0)
    (C : U →ₗ[K] S) (hC : C ∈ jointSymmetrizer B)
    (x : U) (hx : x ≠ 0) (hCx : C x = 0) :
    finrank K Z ≤ (finrank K S - finrank K C.range) * finrank K F := by
  have hi : Function.Injective (B.flip x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    exact (hnz z x hz).resolve_right hx
  have hk : ∀ z, C.range ≤ (B.flip x z).ker := by
    intro z s hs
    obtain ⟨u, rfl⟩ := hs
    change B z x (C u) = 0
    rw [hC z x u, hCx, map_zero]
  simpa only [finrank_top] using
    finrank_le_annihilator_capacity C.range ⊤ (B.flip x) hi (fun _ ↦ le_top) hk

/-- Обратимый симметризатор и ненулевой симметризатор ранга один
ограничивают Z размерностью самого выхода F. -/
theorem jointSymmetrizer_capacity_of_equiv_and_rank_one
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] F)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0)
    (E : U ≃ₗ[K] S) (hE : E.toLinearMap ∈ jointSymmetrizer B)
    (C : U →ₗ[K] S) (hC : C ∈ jointSymmetrizer B)
    (hC1 : finrank K C.range = 1) : finrank K Z ≤ finrank K F := by
  have hC0 : C ≠ 0 := by
    intro hh
    rw [hh, LinearMap.range_zero, finrank_bot] at hC1
    omega
  obtain ⟨v, hv⟩ : ∃ v, C v ≠ 0 := by
    by_contra! hh
    exact hC0 (LinearMap.ext fun x ↦ hh x)
  let x := E.symm (C v)
  have hx : x ≠ 0 := by
    intro hh
    apply hv
    have := congrArg E hh
    simpa [x] using this
  have hi : Function.Injective (B.flip x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    exact (hnz z x hz).resolve_right hx
  let L := C.ker.map E.toLinearMap
  have hk : ∀ z, L ≤ (B.flip x z).ker := by
    intro z s hs
    obtain ⟨u, hu, rfl⟩ := hs
    change B z x (E u) = 0
    have he : B z x (E u) = B z u (E x) := hE z x u
    rw [he]
    simp only [x, LinearEquiv.apply_symm_apply]
    change B z u (C v) = 0
    rw [hC z u v]
    change C u = 0 at hu
    rw [hu, map_zero]
  have hb := finrank_le_annihilator_capacity L ⊤ (B.flip x) hi
    (fun _ ↦ le_top) hk
  have hd := C.finrank_range_add_finrank_ker
  have hL : finrank K L = finrank K C.ker := by
    exact LinearEquiv.finrank_map_eq _ _
  rw [E.finrank_eq, hC1] at hd
  rw [hL] at hb
  simpa only [finrank_top, show finrank K S - finrank K C.ker = 1 by omega,
    one_mul] using hb

omit [FiniteDimensional K U] [FiniteDimensional K F] in
/-- Если совместные симметризаторы имеют общий образ в прямой и dim≥2,
то все значения B зануляют эту прямую. -/
theorem jointSymmetrizer_common_line_le_ker
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] F)
    (H : Submodule K (U →ₗ[K] S)) (hH : H ≤ jointSymmetrizer B)
    (L : Submodule K S) (hL : finrank K L ≤ 1)
    (hr : ∀ C ∈ H, C.range ≤ L) (hd : 2 ≤ finrank K H) :
    ∀ z x, L ≤ (B z x).ker := by
  intro z x
  by_contra hn
  have hb : (B z x).domRestrict L ≠ 0 := by
    intro he
    exact hn (fun s hs ↦ congrArg (fun f : L →ₗ[K] F ↦ f ⟨s, hs⟩) he)
  have hi := linearMap_injective_of_finrank_le_one ((B z x).domRestrict L) hL hb
  let e : H →ₗ[K] L :=
    { toFun C := ⟨C.val x, hr C.val C.property ⟨x, rfl⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he : Function.Injective e := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro C hC
    apply Subtype.ext
    ext y
    have hCx : C.val x = 0 := congrArg Subtype.val hC
    have hh : B z x (C.val y) = 0 := by
      rw [hH C.property z x y, hCx, map_zero]
    exact congrArg Subtype.val (hi (a₁ := ⟨C.val y, hr C.val C.property ⟨y, rfl⟩⟩)
      (a₂ := 0) (by simpa using hh))
  have := LinearMap.finrank_le_finrank_of_injective he
  omega

/-- Общая входная гиперплоскость симметризаторов заставляет вычисление
на любом векторе вне неё инъективно вкладывать H в S. На ненулевом
векторе этой гиперплоскости B зануляет полученный образ. -/
theorem jointSymmetrizer_capacity_of_common_hyperplane
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] F)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0)
    (H : Submodule K (U →ₗ[K] S)) (hH : H ≤ jointSymmetrizer B)
    (N : Submodule K U) (hN : finrank K N + 1 = finrank K U)
    (hN0 : 0 < finrank K N) (hk : ∀ C ∈ H, N ≤ C.ker) :
    finrank K Z ≤ (finrank K S - finrank K H) * finrank K F := by
  have hNt : N ≠ ⊤ := by
    intro hh
    rw [hh, finrank_top] at hN
    omega
  obtain ⟨x, _, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hNt)
  have hsup : N ⊔ Submodule.span K {x} = ⊤ := by
    apply (Submodule.sup_span_singleton_eq_top_iff hx).mpr
    rw [Submodule.finrank_quotient]
    omega
  let e : H →ₗ[K] S := (LinearMap.applyₗ x).comp H.subtype
  have he : Function.Injective e := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro C hC
    apply Subtype.ext
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hsup]
    apply sup_le (hk C.val C.property)
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hC
  have hdim : finrank K e.range = finrank K H := LinearMap.finrank_range_of_inj he
  have hNb : N ≠ ⊥ := by
    intro hh
    rw [hh, finrank_bot] at hN0
    omega
  obtain ⟨u, hu, hu0⟩ := N.ne_bot_iff.mp hNb
  have hi : Function.Injective (B.flip u) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    exact (hnz z u hz).resolve_right hu0
  have hkill : ∀ z, e.range ≤ (B.flip u z).ker := by
    intro z s hs
    obtain ⟨C, rfl⟩ := hs
    change B z u (C.val x) = 0
    rw [hH C.property z u x]
    have hCu : C.val u = 0 := hk C.val C.property hu
    rw [hCu, map_zero]
  simpa only [hdim, finrank_top] using
    finrank_le_annihilator_capacity e.range ⊤ (B.flip u) hi (fun _ ↦ le_top) hkill

omit [FiniteDimensional K U] in
/-- Общая образная прямая двумерного пространства симметризаторов
ограничивает весь линейный образ B отображениями S/L→F. -/
theorem jointSymmetrizer_span_capacity_of_common_line
    (B : Z →ₗ[K] U →ₗ[K] S →ₗ[K] F)
    (H : Submodule K (U →ₗ[K] S)) (hH : H ≤ jointSymmetrizer B)
    (L : Submodule K S) (hL : finrank K L = 1)
    (hr : ∀ C ∈ H, C.range ≤ L) (hd : 2 ≤ finrank K H) :
    finrank K ↥(⨆ z, (B z).range : Submodule K (S →ₗ[K] F)) ≤
      (finrank K S - 1) * finrank K F := by
  let R : (S →ₗ[K] F) →ₗ[K] (L →ₗ[K] F) :=
    { toFun f := f.domRestrict L
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hk := jointSymmetrizer_common_line_le_ker B H hH L hL.le hr hd
  have hBR : (⨆ z, (B z).range) ≤ R.ker := by
    apply iSup_le
    intro z f hf
    obtain ⟨u, rfl⟩ := hf
    ext s
    exact hk z u s.property
  have hb := finrank_le_annihilator_capacity L ⊤
    (⨆ z, (B z).range).subtype Subtype.val_injective (fun _ ↦ le_top)
    (fun f s hs ↦ congrArg (fun g : L →ₗ[K] F ↦ g ⟨s, hs⟩) (hBR f.property))
  simpa only [hL, finrank_top] using hb

end Abstract

section Coordinates
variable {K P S F Z : Type*} [Field K] [IsAlgClosed K]
  [Fintype P] [Fintype S]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup Z] [Module K Z]

/-- Для квадратных размеров n≥3 совместный симметризатор имеет dim≤1,
если dim Z>dim F·(n−2), а весь образ B имеет dim>dim F·(n−1).
Ни координатная алгебра, ни точный алгоритм в этой лемме не участвуют. -/
theorem finrank_jointSymmetrizer_le_one_of_nz_capacity
    (B : Z →ₗ[K] (P → K) →ₗ[K] (S → K) →ₗ[K] F)
    (hPS : Fintype.card P = Fintype.card S) (hn : 3 ≤ Fintype.card S)
    (hnz : ∀ z u, B z u = 0 → z = 0 ∨ u = 0)
    (hZ : (Fintype.card S - 2) * finrank K F < finrank K Z)
    (hB : (Fintype.card S - 1) * finrank K F <
      finrank K ↥(⨆ z, (B z).range : Submodule K ((S → K) →ₗ[K] F))) :
    finrank K (jointSymmetrizer B) ≤ 1 := by
  classical
  let H := jointSymmetrizer B
  have hsing (C : (P → K) →ₗ[K] (S → K)) (hC : C ∈ H)
      (hi : ¬ Function.Injective C) : finrank K C.range ≤ 1 := by
    have hk : C.ker ≠ ⊥ := fun hh ↦ hi (LinearMap.ker_eq_bot.mp hh)
    obtain ⟨u, hu, hu0⟩ := C.ker.ne_bot_iff.mp hk
    have hc := jointSymmetrizer_capacity_of_kernel B hnz C hC u hu0 hu
    simp only [Module.finrank_pi] at hc
    by_contra! hr
    have hs : (Fintype.card S - finrank K C.range) * finrank K F ≤
        (Fintype.card S - 2) * finrank K F :=
      Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hr _)
    omega
  by_cases hinv : ∃ E : (P → K) ≃ₗ[K] (S → K), E.toLinearMap ∈ H
  · obtain ⟨E, hE⟩ := hinv
    have hi : ∀ C : H, C ≠ 0 → Function.Injective C.val := by
      intro C hC
      by_contra hCI
      have hr := hsing C.val C.property hCI
      have hr0 : finrank K C.val.range ≠ 0 := by
        intro hh
        apply hC
        exact Subtype.ext (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hh))
      have hc := jointSymmetrizer_capacity_of_equiv_and_rank_one B hnz E hE C.val
        C.property (by omega)
      have hf : finrank K F ≤ (Fintype.card S - 2) * finrank K F := by
        calc
          finrank K F = 1 * finrank K F := by omega
          _ ≤ (Fintype.card S - 2) * finrank K F := Nat.mul_le_mul_right _ (by omega)
      omega
    let C : (P → K) →ₗ[K] H →ₗ[K] (S → K) := H.subtype.flip
    have : Nontrivial (P → K) := Module.nontrivial_of_finrank_pos (R := K) (by
      simp only [Module.finrank_pi]
      omega)
    exact finrank_right_le_one_of_nonsingular_bilinear
      (K := K) (T := P → K) (U := H) (V := S → K) (by simpa using hPS) C (by
      intro u C' hu
      by_cases hC : C' = 0
      · exact Or.inr hC
      · exact Or.inl (hi C' hC (hu.trans (map_zero C'.val).symm)))
  by_contra! hd
  have hdH : 2 ≤ finrank K H := hd
  let T := H.map rowLinearEquiv.symm.toLinearMap
  have hT (A : Matrix P S K) (hA : A ∈ T) : A.rank ≤ 1 := by
    obtain ⟨C, hC, rfl⟩ := hA
    have hi : ¬ Function.Injective C := by
      intro hi
      exact hinv ⟨LinearEquiv.ofBijective C ⟨hi,
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simpa using hPS)).mp hi⟩, hC⟩
    rw [matrix_rank_eq_finrank_rowRange]
    have he : (rowLinearEquiv.symm.toLinearMap C).vecMulLinear = C := by
      rw [← rowLinearEquiv_apply]
      exact rowLinearEquiv.apply_symm_apply C
    rw [he]
    exact hsing C hC hi
  have hTb : T ≠ ⊥ := by
    intro hh
    have he : finrank K T = finrank K H := LinearEquiv.finrank_map_eq _ _
    rw [hh, finrank_bot] at he
    omega
  obtain ⟨A, hA, hA0⟩ := T.ne_bot_iff.mp hTb
  rcases rank_le_one_space_common_factor T hT with ⟨a, ha⟩ | ⟨s, hs⟩
  · have ha0 : a ≠ 0 := by
      intro hh
      obtain ⟨s, he⟩ := ha A hA
      apply hA0
      rw [← he, hh]
      ext p s
      simp [vecMulVec]
    let φ := dotProductBilin K K a
    have hφ : φ ≠ 0 := by
      intro hh
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by simpa [funext_iff] using ha0
      apply hi
      simpa [φ] using congrArg (fun f : (P → K) →ₗ[K] K ↦ f (Pi.single i 1)) hh
    have hN := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    have hk : ∀ C ∈ H, φ.ker ≤ C.ker := by
      intro C hC u hu
      obtain ⟨s, he⟩ := ha (rowLinearEquiv.symm C) ⟨C, hC, rfl⟩
      have he' : C = rowLinearEquiv (vecMulVec a s) := by rw [he]; simp
      rw [he']
      change φ u = 0 at hu
      rw [rowLinearEquiv_apply]
      change (vecMulVec a s).vecMulLinear u = 0
      have hdot : u ⬝ᵥ a = 0 := by simpa [φ, dotProduct_comm] using hu
      simp [vecMul_vecMulVec, hdot]
    have hc := jointSymmetrizer_capacity_of_common_hyperplane B hnz H le_rfl φ.ker
      hN (by simp only [Module.finrank_pi] at hN; omega) hk
    simp only [Module.finrank_pi] at hc
    have hs : (Fintype.card S - finrank K H) * finrank K F ≤
        (Fintype.card S - 2) * finrank K F :=
      Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hdH _)
    omega
  · have hs0 : s ≠ 0 := by
      intro hh
      obtain ⟨a, he⟩ := hs A hA
      apply hA0
      rw [← he, hh]
      ext p s
      simp [vecMulVec]
    let L := Submodule.span K {s}
    have hL : finrank K L = 1 := finrank_span_singleton hs0
    have hr : ∀ C ∈ H, C.range ≤ L := by
      intro C hC u hu
      obtain ⟨a, he⟩ := hs (rowLinearEquiv.symm C) ⟨C, hC, rfl⟩
      obtain ⟨v, rfl⟩ := hu
      have he' : C = rowLinearEquiv (vecMulVec a s) := by rw [he]; simp
      rw [he']
      simp only [rowLinearEquiv_apply, vecMulLinear_apply, vecMul_vecMulVec]
      exact L.smul_mem _ (Submodule.mem_span_singleton_self s)
    have hc := jointSymmetrizer_span_capacity_of_common_line B H le_rfl L hL hr hdH
    simp only [Module.finrank_pi] at hc
    omega

end Coordinates
end MMRank
