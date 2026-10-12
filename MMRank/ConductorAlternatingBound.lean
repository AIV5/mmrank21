import MMRank.ConductorOrthogonality
import MMRank.SmallGrowthLocalization
import MMRank.BasisExtension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Два кондуктора через знакопеременную форму

Вычитание графиков умножения имеет
ядром кондуктор. Два образа ортогональны в пространстве удвоенной размерности;
неравенство получается из ранга и дефекта. Комплекс роста не используется.
-/
namespace MMRank
open Module Matrix
variable {K I : Type*} [Field K] [Fintype I]

-- Вычитание двух графиков; ядро восстанавливает общий прообраз N.
def conductorProjection (x y : I → K) (N : Submodule K (I → K)) :
    (Fin 3 → N) →ₗ[K] (Fin 2 × I → K) where
  toFun v ji := ![(v 1).val - x * (v 0).val, (v 2).val - y * (v 0).val] ji.1 ji.2
  map_add' := by
    intro v w; funext ⟨j,i⟩; fin_cases j <;> simp <;> ring
  map_smul' := by
    intro a v; funext ⟨j,i⟩; fin_cases j <;> simp <;> ring

omit [Fintype I] in
lemma mem_conductor_span_three (x y z : I → K) (N : Submodule K (I → K)) :
    z ∈ conductor N (Submodule.span K (Set.range ![1,x,y])) ↔
      z ∈ N ∧ x*z ∈ N ∧ y*z ∈ N := by
  rw [mem_conductor]
  constructor
  · intro hz
    have hj (j : Fin 3) := hz _ (Submodule.subset_span ⟨j,rfl⟩)
    exact ⟨by simpa using hj 0, by simpa using hj 1, by simpa using hj 2⟩
  · rintro ⟨hz,hx,hy⟩ m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨j,rfl⟩ := hm
      fin_cases j
      · simpa using hz
      · simpa using hx
      · simpa using hy
    | zero => simp
    | add a b _ _ ha hb => simpa [add_mul] using N.add_mem ha hb
    | smul a b _ hb => simpa [smul_mul_assoc] using N.smul_mem a hb

noncomputable def conductorProjectionKernelEquiv (x y : I → K) (N : Submodule K (I → K)) :
    (conductorProjection x y N).ker ≃ₗ[K]
      conductor N (Submodule.span K (Set.range ![1,x,y])) where
  toFun v := ⟨(v.val 0).val, by
    apply (mem_conductor_span_three x y _ N).mpr
    have he := v.property
    have hx : (v.val 1).val = x * (v.val 0).val := by
      funext i
      have hi := congrFun he (0,i)
      exact sub_eq_zero.mp hi
    have hy : (v.val 2).val = y * (v.val 0).val := by
      funext i
      have hi := congrFun he (1,i)
      exact sub_eq_zero.mp hi
    exact ⟨(v.val 0).property, hx ▸ (v.val 1).property, hy ▸ (v.val 2).property⟩⟩
  invFun z := ⟨![⟨z.val, ((mem_conductor_span_three x y _ N).mp z.property).1⟩,
    ⟨x*z.val, ((mem_conductor_span_three x y _ N).mp z.property).2.1⟩,
    ⟨y*z.val, ((mem_conductor_span_three x y _ N).mp z.property).2.2⟩], by
      ext ⟨j,i⟩; fin_cases j <;> simp [conductorProjection]⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    funext i
    have h0 := congrFun v.property (0,i)
    have h1 := congrFun v.property (1,i)
    fin_cases j <;> simp_all [conductorProjection, sub_eq_zero]
  right_inv z := by apply Subtype.ext; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Поворот, превращающий стандартное спаривание в знакопеременное. -/
def symplecticRotation : (Fin 2 × I → K) ≃ₗ[K] (Fin 2 × I → K) where
  toFun v ji := ![v (1,ji.2), -v (0,ji.2)] ji.1
  invFun v ji := ![-v (1,ji.2), v (0,ji.2)] ji.1
  left_inv v := by funext ⟨j,i⟩; fin_cases j <;> simp
  right_inv v := by funext ⟨j,i⟩; fin_cases j <;> simp
  map_add' := by intros; funext ⟨j,i⟩; fin_cases j <;> simp [add_comm]
  map_smul' := by intros; funext ⟨j,i⟩; fin_cases j <;> simp

lemma conductorProjection_orthogonal (x y : I → K) (N B : Submodule K (I → K))
    (hB : B ≤ coordinateOrthogonal ((Submodule.span K (Set.range ![1,x,y])) * N))
    (n : Fin 3 → N) (b : Fin 3 → B) :
    conductorProjection x y N n ⬝ᵥ symplecticRotation (conductorProjection x y B b) = 0 := by
  have hz (j k : Fin 3) (a : Fin 3) : (![1,x,y] a * (n j).val) ⬝ᵥ (b k).val = 0 :=
    Submodule.mem_orthogonalBilin.mp (hB (b k).property) _
      (Submodule.mul_mem_mul (Submodule.subset_span ⟨a,rfl⟩) (n j).property)
  have h0 (j k : Fin 3) : (n j).val ⬝ᵥ (b k).val = 0 := by simpa using hz j k 0
  have hx (j k : Fin 3) : (x * (n j).val) ⬝ᵥ (b k).val = 0 := by simpa using hz j k 1
  have hy (j k : Fin 3) : (y * (n j).val) ⬝ᵥ (b k).val = 0 := by simpa using hz j k 2
  calc
    _ = (n 1).val ⬝ᵥ (b 2).val - (y * (n 1).val) ⬝ᵥ (b 0).val -
        (x * (n 0).val) ⬝ᵥ (b 2).val - (n 2).val ⬝ᵥ (b 1).val +
        (x * (n 2).val) ⬝ᵥ (b 0).val + (y * (n 0).val) ⬝ᵥ (b 1).val := by
      simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
        conductorProjection, LinearMap.coe_mk, AddHom.coe_mk, symplecticRotation,
        LinearEquiv.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.sub_apply, Pi.mul_apply]
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [h0,h0,hx,hx,hy,hy]; ring

/-- Достаточно двух направлений помимо единицы; их независимость не нужна. -/
theorem two_conductor_dimension_sum_bound_of_span (x y : I → K) (N B : Submodule K (I → K))
    (hB : B ≤ coordinateOrthogonal ((Submodule.span K (Set.range ![1,x,y])) * N)) :
    3 * finrank K N + 3 * finrank K B ≤
      finrank K (conductor N (Submodule.span K (Set.range ![1,x,y]))) +
      finrank K (conductor B (Submodule.span K (Set.range ![1,x,y]))) + 2 * Fintype.card I := by
  let f := conductorProjection x y N
  let g := conductorProjection x y B
  have horth : g.range.map symplecticRotation.toLinearMap ≤ coordinateOrthogonal f.range := by
    rintro _ ⟨_, ⟨b,rfl⟩, rfl⟩
    apply Submodule.mem_orthogonalBilin.mpr
    rintro _ ⟨n,rfl⟩
    exact conductorProjection_orthogonal x y N B hB n b
  have hb := Submodule.finrank_mono horth
  rw [LinearEquiv.finrank_map_eq, finrank_coordinateOrthogonal, Fintype.card_prod,
    Fintype.card_fin] at hb
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  rw [(conductorProjectionKernelEquiv x y N).finrank_eq] at hf
  rw [(conductorProjectionKernelEquiv x y B).finrank_eq] at hg
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hf hg
  have hle := f.range.finrank_le
  simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin] at hle
  omega

/-- Унитальное трёхмерное пространство порождается единицей и двумя элементами. -/
theorem exists_pair_span_of_one_mem_finrank_three (M : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M) (hM : finrank K M = 3) :
    ∃ x y : I → K, M = Submodule.span K (Set.range ![1,x,y]) := by
  have hm := M.finrank_le
  rw [Module.finrank_pi,hM] at hm
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b,j,hj⟩ := exists_basis_containing_nonzero
    (finBasisOfFinrankEq K M hM) (⟨1,h1⟩ : M) (by
      intro hz
      exact one_ne_zero (congrArg Subtype.val hz))
  let b' := b.reindex (Equiv.swap j 0)
  have h0 : (b' 0).val = 1 := by simp [b',hj]
  have he : (fun k ↦ (b' k).val) = ![1,(b' 1).val,(b' 2).val] := by
    funext k; fin_cases k <;> simp [h0]
  refine ⟨(b' 1).val,(b' 2).val,?_⟩
  rw [← he]
  change M = Submodule.span K (Set.range (M.subtype ∘ b'))
  rw [Set.range_comp,Submodule.span_image,b'.span_eq,Submodule.map_subtype_top]

/-- Прежняя оценка при dim M=3, теперь без комплекса роста. -/
theorem two_conductor_dimension_sum_bound (M N B : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M) (hM : finrank K M = 3)
    (hB : B ≤ coordinateOrthogonal (M * N)) :
    3 * finrank K N + finrank K B ≤
      finrank K (conductor N M) + finrank K (conductor B M) +
        2 * (Fintype.card I - finrank K B) := by
  obtain ⟨x,y,hxy⟩ := exists_pair_span_of_one_mem_finrank_three M h1 hM
  have hb := B.finrank_le
  rw [Module.finrank_pi] at hb
  have hh := two_conductor_dimension_sum_bound_of_span x y N B (by simpa only [← hxy] using hB)
  rw [← hxy] at hh
  omega

/-- Усиленная нижняя оценка кондуктора из полного носителя пространства отношений.
Это общий линейно-алгебраический результат, не теорема о ранге матричного умножения. -/
theorem conductor_bound_of_noPointWords (M N B : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M) (hM : finrank K M = 3)
    (hB : B ≤ coordinateOrthogonal (M * N)) (hbdim : 2 ≤ finrank K B)
    (hsupp : ∀ i, ∃ b ∈ B, b i ≠ 0) (hn : HasNoPointWords M B) :
    3 * finrank K N + 2 ≤
      finrank K (conductor N M) + 2 * (Fintype.card I - finrank K B) := by
  have hd := two_conductor_dimension_sum_bound M N B h1 hM hB
  have hb := two_le_conductor_boundary_of_noPointWords M B h1 (by omega) hbdim hsupp hn
  omega

/-- Вариант для уже проверенного отсутствия делителей нуля M×B. -/
theorem conductor_bound_of_noZeroDivisors (M N B : Submodule K (I → K))
    (h1 : (1 : I → K) ∈ M) (hM : finrank K M = 3)
    (hB : B ≤ coordinateOrthogonal (M * N)) (hbdim : 2 ≤ finrank K B)
    (hsupp : ∀ i, ∃ b ∈ B, b i ≠ 0)
    (hnz : ∀ a ∈ M, ∀ b ∈ B, a * b = 0 → a = 0 ∨ b = 0) :
    3 * finrank K N + 2 ≤
      finrank K (conductor N M) + 2 * (Fintype.card I - finrank K B) :=
  conductor_bound_of_noPointWords M N B h1 hM hB hbdim hsupp
    (hasNoPointWords_of_noZeroDivisors M B (by omega) hnz)

end MMRank
