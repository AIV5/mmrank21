import MMRank.RankOneFamilyRigidity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin

/-! # Конечная геометрия трёх лучей

Используются попарно независимые векторы и подпространства размерностей один и два.
-/

namespace MMRank
open Module Submodule
open scoped BigOperators Classical

variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [DecidableEq I]

omit [FiniteDimensional K E] in
/-- Конечное покрытие оплачивает число точек суммой размеров классов. -/
theorem card_le_sum_cards_of_cover {J : Type*} [Fintype J]
    (s : Finset I) (t : J → Finset I) (h : ∀ i ∈ s, ∃ j, i ∈ t j) :
    s.card ≤ ∑ j, (t j).card := by
  classical
  exact (Finset.card_le_card (show s ⊆ Finset.univ.biUnion t from
    fun i hi ↦ let ⟨j, hj⟩ := h i hi
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩)).trans
    Finset.card_biUnion_le

/-- В одномерном подпространстве помещается не более одного представителя
попарно различных проективных направлений. -/
theorem card_filter_mem_le_one_of_finrank_le_one
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (s : Finset I) (L : Submodule K E) (hL : finrank K L ≤ 1) :
    (s.filter fun i ↦ μ i ∈ L).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hli : LinearIndependent K (![⟨μ i, (Finset.mem_filter.mp hi).2⟩,
      ⟨μ j, (Finset.mem_filter.mp hj).2⟩] : Fin 2 → L) := by
    apply LinearIndependent.of_comp L.subtype
    convert hp hij using 1
    ext a; fin_cases a <;> rfl
  have hm := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hm
  omega

/-- Четыре различные пересечения двух пар плоскостей покрывают максимум
четыре индекса. Не требуется различать или нумеровать сами точки. -/
theorem card_le_four_of_mem_two_plane_pairs
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (s : Finset I)
    (A B : Fin 2 → Submodule K E)
    (hA : ∀ a, finrank K (A a) = 2) (hB : ∀ b, finrank K (B b) = 2)
    (hne : ∀ a b, A a ≠ B b)
    (hcover : ∀ i ∈ s, (∃ a, μ i ∈ A a) ∧ ∃ b, μ i ∈ B b) :
    s.card ≤ 4 := by
  classical
  let t (p : Fin 2 × Fin 2) := s.filter fun i ↦ μ i ∈ A p.1 ⊓ B p.2
  have ht (p : Fin 2 × Fin 2) : (t p).card ≤ 1 := by
    apply card_filter_mem_le_one_of_finrank_le_one μ hp s _
    exact (planes_sup_eq_top_and_finrank_inf hE _ _ (hA p.1) (hB p.2)
      (hne p.1 p.2)).2.le
  have hs : s.card ≤ ∑ p, (t p).card := by
    apply card_le_sum_cards_of_cover
    intro i hi
    obtain ⟨⟨a, ha⟩, b, hb⟩ := hcover i hi
    exact ⟨(a,b), Finset.mem_filter.mpr ⟨hi, ha, hb⟩⟩
  calc
    s.card ≤ ∑ p : Fin 2 × Fin 2, (t p).card := hs
    _ ≤ ∑ _p : Fin 2 × Fin 2, 1 := Finset.sum_le_sum (fun p _ ↦ ht p)
    _ = 4 := by simp

/-- Две разные прямые в плоскости порождают эту плоскость. -/
theorem sup_eq_plane_of_distinct_lines
    (C D P : Submodule K E) (hC : finrank K C = 1) (hD : finrank K D = 1)
    (hP : finrank K P = 2) (hCP : C ≤ P) (hDP : D ≤ P) (hne : C ≠ D) :
    C ⊔ D = P := by
  have hs : C ⊔ D ≤ P := sup_le hCP hDP
  have hu : finrank K (C ⊔ D : Submodule K E) ≤ 2 := by
    have hh := Submodule.finrank_mono hs
    omega
  have hl : 2 ≤ finrank K (C ⊔ D : Submodule K E) := by
    by_contra hn
    have hc : C = C ⊔ D :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have hd : D = C ⊔ D :=
      Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
    exact hne (hc.trans hd.symm)
  exact Submodule.eq_of_le_of_finrank_eq hs (by omega)

/-- Общий бюджет двух пар внешних плоскостей через разные центры.
Лемма четырёх пересечений. -/
theorem card_le_four_of_two_centers_in_plane
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (s : Finset I)
    (C D P : Submodule K E) (hC : finrank K C = 1) (hD : finrank K D = 1)
    (hP : finrank K P = 2) (hCP : C ≤ P) (hDP : D ≤ P) (hCD : C ≠ D)
    (A B : Fin 2 → Submodule K E)
    (hA : ∀ a, finrank K (A a) = 2) (hB : ∀ b, finrank K (B b) = 2)
    (hCA : ∀ a, C ≤ A a) (hDB : ∀ b, D ≤ B b)
    (hAP : ∀ a, A a ≠ P)
    (hcover : ∀ i ∈ s, (∃ a, μ i ∈ A a) ∧ ∃ b, μ i ∈ B b) :
    s.card ≤ 4 := by
  apply card_le_four_of_mem_two_plane_pairs μ hp hE s A B hA hB
  · intro a b hab
    have hs : P ≤ A a := by
      rw [← sup_eq_plane_of_distinct_lines C D P hC hD hP hCP hDP hCD]
      exact sup_le (hCA a) (hab ▸ hDB b)
    have he : P = A a := Submodule.eq_of_le_of_finrank_eq hs (by rw [hP, hA])
    exact hAP a he.symm
  · exact hcover

/-- Разные равномерные блоки с
пересечениями размера ≤ 1 используют непересекающиеся упорядоченные пары.
Число точек, размер блока и окружающая геометрия произвольны. -/
theorem card_uniform_blocks_mul_le_offDiag
    (s : Finset I) (B : Finset (Finset I)) (k : ℕ)
    (hsub : ∀ b ∈ B, b ⊆ s) (hcard : ∀ b ∈ B, b.card = k)
    (hlinear : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → (b ∩ c).card ≤ 1) :
    B.card * (k * k - k) ≤ s.card * s.card - s.card := by
  classical
  have hd : (B : Set (Finset I)).PairwiseDisjoint Finset.offDiag := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro p hpb hpc
    obtain ⟨hib, hjb, hij⟩ := Finset.mem_offDiag.mp hpb
    obtain ⟨hic, hjc, _⟩ := Finset.mem_offDiag.mp hpc
    exact hij (Finset.card_le_one.mp (hlinear b hb c hc hbc) p.1
      (Finset.mem_inter.mpr ⟨hib, hic⟩) p.2 (Finset.mem_inter.mpr ⟨hjb, hjc⟩))
  have hsub' : B.biUnion Finset.offDiag ⊆ s.offDiag := by
    intro p hp
    obtain ⟨b, hb, hpb⟩ := Finset.mem_biUnion.mp hp
    exact Finset.offDiag_mono (hsub b hb) hpb
  have hbudget := Finset.card_le_card hsub'
  rw [Finset.card_biUnion hd] at hbudget
  have hsum : ∑ b ∈ B, b.offDiag.card = B.card * (k * k - k) := by
    calc
      _ = ∑ _b ∈ B, (k * k - k) := Finset.sum_congr rfl (fun b hb ↦ by
        rw [Finset.offDiag_card, hcard b hb])
      _ = _ := by simp
  rwa [hsum, Finset.offDiag_card] at hbudget

omit [FiniteDimensional K E] [DecidableEq I] in
/-- Две независимые точки порождают содержащую их двумерную плоскость. -/
theorem span_pair_eq_of_mem_plane (P : Submodule K E) (hP : finrank K P = 2)
    (u v : E) (hu : u ∈ P) (hv : v ∈ P)
    (hli : LinearIndependent K ![u, v]) : Submodule.span K {u, v} = P := by
  let : FiniteDimensional K P := Module.finite_of_finrank_pos (by omega)
  have hd : finrank K (Submodule.span K ({u, v} : Set E)) = 2 := by
    have hr : Set.range (![u, v] : Fin 2 → E) = {u, v} := by
      ext z; simp [eq_comm, or_comm]
    rw [← hr]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli
  exact Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (Set.insert_subset_iff.mpr
      ⟨hu, Set.singleton_subset_iff.mpr hv⟩)) (hd.trans hP.symm)

omit [FiniteDimensional K E] [DecidableEq I] in
/-- Две плоскости, содержащие два независимых представителя, совпадают. -/
theorem plane_eq_of_two_vectors_mem
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (P Q : Submodule K E) (hP : finrank K P = 2) (hQ : finrank K Q = 2)
    {i j : I} (hij : i ≠ j) (hiP : μ i ∈ P) (hjP : μ j ∈ P)
    (hiQ : μ i ∈ Q) (hjQ : μ j ∈ Q) : P = Q := by
  exact (span_pair_eq_of_mem_plane P hP _ _ hiP hjP (hp hij)).symm.trans
    (span_pair_eq_of_mem_plane Q hQ _ _ hiQ hjQ (hp hij))

/-- Если точки покрыты n плоскостями, то любая другая плоскость содержит
не более n точек. -/
theorem card_filter_mem_plane_le_of_plane_cover {n : ℕ}
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (s : Finset I) (P : Submodule K E)
    (hP : finrank K P = 2) (A : Fin n → Submodule K E)
    (hA : ∀ a, finrank K (A a) = 2) (hne : ∀ a, A a ≠ P)
    (hcover : ∀ i ∈ s, ∃ a, μ i ∈ A a) :
    (s.filter fun i ↦ μ i ∈ P).card ≤ n := by
  classical
  let t (a : Fin n) := s.filter fun i ↦ μ i ∈ A a ⊓ P
  have ht (a : Fin n) : (t a).card ≤ 1 := by
    apply card_filter_mem_le_one_of_finrank_le_one μ hp s _
    exact (planes_sup_eq_top_and_finrank_inf hE _ _ (hA a) hP (hne a)).2.le
  have hs : (s.filter fun i ↦ μ i ∈ P).card ≤ ∑ a, (t a).card := by
    apply card_le_sum_cards_of_cover
    intro i hi
    obtain ⟨his, hiP⟩ := Finset.mem_filter.mp hi
    obtain ⟨a, ha⟩ := hcover i his
    exact ⟨a, Finset.mem_filter.mpr ⟨his, ha, hiP⟩⟩
  calc
    _ ≤ ∑ a : Fin n, (t a).card := hs
    _ ≤ ∑ _a : Fin n, 1 := Finset.sum_le_sum (fun a _ ↦ ht a)
    _ = n := by simp

/-- Геометрический сертификат центра трёх лучей; множества индексов
задаются принадлежностью двумерным подпространствам. -/
structure ThreeRayCover (μ : I → E) (s : Finset I) (C : Submodule K E) where
  finrank_center : finrank K C = 1
  ray : Fin 3 → Submodule K E
  finrank_ray : ∀ a, finrank K (ray a) = 2
  ray_injective : Function.Injective ray
  center_le_ray : ∀ a, C ≤ ray a
  cover : ∀ i ∈ s, ∃ a, μ i ∈ ray a
  active : ∀ a, 2 ≤ (s.filter fun i ↦ μ i ∈ ray a ∧ μ i ∉ C).card

/-- Плоскость с четырьмя точками обязательно является одним из лучей
каждого центра. -/
theorem ThreeRayCover.plane_is_ray_of_four_points
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C)
    (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (P : Submodule K E) (hP : finrank K P = 2)
    (hrich : 4 ≤ (s.filter fun i ↦ μ i ∈ P).card) :
    ∃ a, H.ray a = P := by
  by_contra hn
  have hb := card_filter_mem_plane_le_of_plane_cover μ hp hE s P hP
    H.ray H.finrank_ray (fun a ha ↦ hn ⟨a, ha⟩) H.cover
  omega

omit [DecidableEq I] in
/-- Пересечение разных лучей или луча с другой плоскостью через центр
совпадает с самим центром. -/
theorem ThreeRayCover.inf_plane_eq_center
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C) (hE : finrank K E = 3)
    (P : Submodule K E) (hP : finrank K P = 2) (hCP : C ≤ P)
    (a : Fin 3) (hne : H.ray a ≠ P) : H.ray a ⊓ P = C := by
  have hc : C ≤ H.ray a ⊓ P := le_inf (H.center_le_ray a) hCP
  have hi := (planes_sup_eq_top_and_finrank_inf hE _ _ (H.finrank_ray a) hP hne).2
  exact (Submodule.eq_of_le_of_finrank_eq hc (H.finrank_center.trans hi.symm)).symm

omit [DecidableEq I] in
/-- Активная точка принадлежит только одному лучу данного центра. -/
theorem ThreeRayCover.active_ray_unique
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C) (hE : finrank K E = 3)
    {a b : Fin 3} {i : I} (hia : μ i ∈ H.ray a) (hib : μ i ∈ H.ray b)
    (hiC : μ i ∉ C) : a = b := by
  by_contra hab
  have he := H.inf_plane_eq_center hE (H.ray b) (H.finrank_ray b)
    (H.center_le_ray b) a (fun h ↦ hab (H.ray_injective h))
  exact hiC (he ▸ (show μ i ∈ H.ray a ⊓ H.ray b from ⟨hia, hib⟩))

/-- Два центра, имеющие общий луч, оставляют за пределами этого луча
максимум четыре точки. -/
theorem ThreeRayCover.card_outside_common_ray_le_four
    {μ : I → E} {s : Finset I} {C D : Submodule K E}
    (H : ThreeRayCover μ s C) (G : ThreeRayCover μ s D)
    (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (hCD : C ≠ D) (a b : Fin 3)
    (hab : H.ray a = G.ray b) :
    (s.filter fun i ↦ μ i ∉ H.ray a).card ≤ 4 := by
  apply card_le_four_of_two_centers_in_plane μ hp hE _ C D (H.ray a)
    H.finrank_center G.finrank_center (H.finrank_ray a) (H.center_le_ray a)
    (hab.symm ▸ G.center_le_ray b) hCD
    (fun t ↦ H.ray (a.succAbove t)) (fun t ↦ G.ray (b.succAbove t))
    (fun t ↦ H.finrank_ray _) (fun t ↦ G.finrank_ray _)
    (fun t ↦ H.center_le_ray _) (fun t ↦ G.center_le_ray _)
  · intro t ht
    exact Fin.succAbove_ne a t (H.ray_injective ht)
  · intro i hi
    obtain ⟨his, hiP⟩ := Finset.mem_filter.mp hi
    obtain ⟨j, hj⟩ := H.cover i his
    obtain ⟨k, hk⟩ := G.cover i his
    have hja : j ≠ a := by rintro rfl; exact hiP hj
    have hkb : k ≠ b := by
      rintro rfl
      exact hiP (hab.symm ▸ hk)
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hja
    obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq hkb
    exact ⟨⟨t, ht.symm ▸ hj⟩, u, hu.symm ▸ hk⟩

/-- Уже две точки из первой плоскости, лежащие во второй, определяют
равенство плоскостей. -/
theorem plane_eq_of_support_subset_of_two
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (s : Finset I) (P Q : Submodule K E)
    (hP : finrank K P = 2) (hQ : finrank K Q = 2)
    (hsub : (s.filter fun i ↦ μ i ∈ P) ⊆ s.filter fun i ↦ μ i ∈ Q)
    (hcard : 2 ≤ (s.filter fun i ↦ μ i ∈ P).card) : P = Q := by
  by_contra hne
  have hi := (planes_sup_eq_top_and_finrank_inf hE _ _ hP hQ hne).2
  have hs : (s.filter fun i ↦ μ i ∈ P) ⊆ s.filter fun i ↦ μ i ∈ P ⊓ Q := by
    intro i him
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp him).1,
      (Finset.mem_filter.mp him).2, (Finset.mem_filter.mp (hsub him)).2⟩
  have hm := Finset.card_le_card hs
  have ho := card_filter_mem_le_one_of_finrank_le_one μ hp s (P ⊓ Q) hi.le
  omega

omit [FiniteDimensional K E] in
/-- На восьми точках каждый центр с лучами размера не больше трёх имеет
как минимум два луча размера ровно три. -/
theorem ThreeRayCover.exists_two_triple_rays
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C) (hs : s.card = 8)
    (hsmall : ∀ a, (s.filter fun i ↦ μ i ∈ H.ray a).card ≤ 3) :
    ∃ a b : Fin 3, a ≠ b ∧
      (s.filter fun i ↦ μ i ∈ H.ray a).card = 3 ∧
      (s.filter fun i ↦ μ i ∈ H.ray b).card = 3 := by
  classical
  let t (a : Fin 3) := s.filter fun i ↦ μ i ∈ H.ray a
  have hb : 8 ≤ (t 0).card + (t 1).card + (t 2).card := by
    have hb := card_le_sum_cards_of_cover s t (fun i hi ↦
      let ⟨a, ha⟩ := H.cover i hi
      ⟨a, Finset.mem_filter.mpr ⟨hi, ha⟩⟩)
    simpa [hs, Fin.sum_univ_succ, add_assoc] using hb
  have h0 := hsmall 0
  have h1 := hsmall 1
  have h2 := hsmall 2
  have hc : ((t 0).card = 3 ∧ (t 1).card = 3) ∨
      ((t 0).card = 3 ∧ (t 2).card = 3) ∨
      ((t 1).card = 3 ∧ (t 2).card = 3) := by
    change (t 0).card ≤ 3 at h0
    change (t 1).card ≤ 3 at h1
    change (t 2).card ≤ 3 at h2
    omega
  rcases hc with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 1, by decide, h0, h1⟩
  · exact ⟨0, 2, by decide, h0, h2⟩
  · exact ⟨1, 2, by decide, h1, h2⟩

/-- Пять центров невозможны на восьми точках, если в каждой плоскости
лежит не более трёх точек. Десять тройных блоков используют 60 разных
упорядоченных пар, а на восьми точках имеется только 56. -/
theorem not_five_three_ray_covers_of_card_eight_of_plane_bound
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (s : Finset I) (hs : s.card = 8)
    (C : Fin 5 → Submodule K E) (hC : Function.Injective C)
    (H : ∀ c, ThreeRayCover μ s (C c))
    (hsmall : ∀ P : Submodule K E, finrank K P = 2 →
      (s.filter fun i ↦ μ i ∈ P).card ≤ 3) : False := by
  classical
  choose a b hab ha hb using fun c ↦
    (H c).exists_two_triple_rays hs (fun j ↦ hsmall _ ((H c).finrank_ray j))
  let R (p : Fin 5 × Fin 2) := (H p.1).ray (![a p.1, b p.1] p.2)
  let f (p : Fin 5 × Fin 2) := s.filter fun i ↦ μ i ∈ R p
  have hR (p : Fin 5 × Fin 2) : finrank K (R p) = 2 := (H p.1).finrank_ray _
  have hf (p : Fin 5 × Fin 2) : (f p).card = 3 := by
    rcases p with ⟨c, j⟩
    fin_cases j
    · exact ha c
    · exact hb c
  have hinj : Function.Injective f := by
    intro p q hpq
    have hplane : R p = R q := plane_eq_of_support_subset_of_two μ hp hE s _ _
      (hR p) (hR q) (by change f p ⊆ f q; rw [hpq]) (by change 2 ≤ (f p).card; rw [hf]; decide)
    have hcent : p.1 = q.1 := by
      by_contra hne
      have hcentne : C p.1 ≠ C q.1 := fun he ↦ hne (hC he)
      have hbound := ThreeRayCover.card_outside_common_ray_le_four
        (H p.1) (H q.1) hp hE hcentne (![a p.1, b p.1] p.2)
        (![a q.1, b q.1] q.2) hplane
      have hsum := Finset.card_filter_add_card_filter_not (s := s)
        (fun i ↦ μ i ∈ R p)
      change (f p).card + (s.filter fun i ↦ μ i ∉ R p).card = s.card at hsum
      change (s.filter fun i ↦ μ i ∉ R p).card ≤ 4 at hbound
      have hp3 := hf p
      omega
    have hindex : ![a p.1, b p.1] p.2 = ![a p.1, b p.1] q.2 := by
      rcases p with ⟨c, j⟩
      rcases q with ⟨d, k⟩
      change c = d at hcent
      subst d
      exact (H c).ray_injective hplane
    have hpair : Function.Injective (![a p.1, b p.1] : Fin 2 → Fin 3) :=
      Matrix.injective_pair_iff_ne.mpr (hab p.1)
    exact Prod.ext hcent (hpair hindex)
  have hcount : (Finset.univ.image f).card = 10 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hbudget := card_uniform_blocks_mul_le_offDiag s (Finset.univ.image f) 3
    (by
      intro b hb
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.filter_subset _ _)
    (by
      intro b hb
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hb
      exact hf p)
    (by
      intro b hb c hc hbc
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hc
      have hne : R p ≠ R q := by
        intro h
        apply hbc
        dsimp only [f]
        rw [h]
      have hi := (planes_sup_eq_top_and_finrank_inf hE _ _ (hR p) (hR q) hne).2
      have hsub : f p ∩ f q ⊆ s.filter fun i ↦ μ i ∈ R p ⊓ R q := by
        intro i hi
        obtain ⟨hip, hiq⟩ := Finset.mem_inter.mp hi
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hip).1,
          (Finset.mem_filter.mp hip).2, (Finset.mem_filter.mp hiq).2⟩
      exact (Finset.card_le_card hsub).trans
        (card_filter_mem_le_one_of_finrank_le_one μ hp s _ hi.le))
  rw [hcount, hs] at hbudget
  omega

/-- Для точки вне луча имеется другая точка вне того же луча на её луче.
Это конечная версия выбора партнёра во внешнем разбиении. -/
theorem ThreeRayCover.exists_partner_outside_ray
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C) (hE : finrank K E = 3) (a : Fin 3)
    {i : I} (his : i ∈ s) (hia : μ i ∉ H.ray a) :
    ∃ b : Fin 3, ∃ j ∈ s, j ≠ i ∧ μ i ∈ H.ray b ∧
      μ j ∈ H.ray b ∧ μ j ∉ H.ray a := by
  classical
  obtain ⟨b, hib⟩ := H.cover i his
  have hba : b ≠ a := by rintro rfl; exact hia hib
  let t := s.filter fun j ↦ μ j ∈ H.ray b ∧ μ j ∉ C
  have ht := H.active b
  change 2 ≤ t.card at ht
  have hiC : μ i ∉ C := fun hi ↦ hia (H.center_le_ray a hi)
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨his, hib, hiC⟩
  have hnon : (t.erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hit]
    omega
  obtain ⟨j, hj⟩ := hnon
  obtain ⟨hji, hjt⟩ := Finset.mem_erase.mp hj
  obtain ⟨hjs, hjb, hjC⟩ := Finset.mem_filter.mp hjt
  refine ⟨b, j, hjs, hji, hib, hjb, ?_⟩
  intro hja
  exact hba (H.active_ray_unique hE hjb hja hjC)

/-- Плоскость с четырьмя точками допускает не более трёх центров.
При пяти внешних точках уже два разных центра невозможны; при четырёх
каждый центр однозначно задаёт партнёра фиксированной внешней точки. -/
theorem not_five_three_ray_covers_of_rich_plane
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (s : Finset I)
    (C : Fin 5 → Submodule K E) (hC : Function.Injective C)
    (H : ∀ c, ThreeRayCover μ s (C c))
    (P : Submodule K E) (hP : finrank K P = 2)
    (hrich : 4 ≤ (s.filter fun i ↦ μ i ∈ P).card) : False := by
  classical
  choose a ha using fun c ↦ (H c).plane_is_ray_of_four_points hp hE P hP hrich
  let out := s.filter fun i ↦ μ i ∉ P
  have h01 : C 0 ≠ C 1 := fun he ↦ (by decide : (0 : Fin 5) ≠ 1) (hC he)
  have hup := ThreeRayCover.card_outside_common_ray_le_four (H 0) (H 1) hp hE h01
    (a 0) (a 1) ((ha 0).trans (ha 1).symm)
  rw [ha 0] at hup
  change out.card ≤ 4 at hup
  have hactive := (H 0).active ((a 0).succAbove 0)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 <
    (s.filter fun i ↦ μ i ∈ (H 0).ray ((a 0).succAbove 0) ∧ μ i ∉ C 0).card)
  obtain ⟨his, hiray, hiC⟩ := Finset.mem_filter.mp hi
  have hiP : μ i ∉ P := by
    intro hiP
    exact Fin.succAbove_ne (a 0) 0
      ((H 0).active_ray_unique hE hiray (by rwa [ha 0]) hiC)
  have hiout : i ∈ out := Finset.mem_filter.mpr ⟨his, hiP⟩
  have hpart (c : Fin 5) : ∃ b : Fin 3, ∃ j ∈ s, j ≠ i ∧ μ i ∈ (H c).ray b ∧
      μ j ∈ (H c).ray b ∧ μ j ∉ P := by
    obtain ⟨b, j, hjs, hji, hib, hjb, hjP⟩ := (H c).exists_partner_outside_ray hE
      (a c) his (by rwa [ha c])
    exact ⟨b, j, hjs, hji, hib, hjb, by rwa [ha c] at hjP⟩
  choose b j hjs hji hib hjb hjP using hpart
  have hjout (c : Fin 5) : j c ∈ out.erase i := by
    exact Finset.mem_erase.mpr ⟨hji c, Finset.mem_filter.mpr ⟨hjs c, hjP c⟩⟩
  have hjinj : Function.Injective j := by
    intro c d hcd
    have hplanes : (H c).ray (b c) = (H d).ray (b d) :=
      plane_eq_of_two_vectors_mem μ hp _ _ ((H c).finrank_ray _) ((H d).finrank_ray _)
        (hji c).symm (hib c) (hjb c) (hib d) (hcd.symm ▸ hjb d)
    have hPc : C c ≤ P := ha c ▸ (H c).center_le_ray (a c)
    have hPd : C d ≤ P := ha d ▸ (H d).center_le_ray (a d)
    have hneqc : (H c).ray (b c) ≠ P := by intro he; exact hiP (he ▸ hib c)
    have hneqd : (H d).ray (b d) ≠ P := by intro he; exact hiP (he ▸ hib d)
    have hec := (H c).inf_plane_eq_center hE P hP hPc (b c) hneqc
    have hed := (H d).inf_plane_eq_center hE P hP hPd (b d) hneqd
    apply hC
    exact hec.symm.trans ((congrArg (fun Q : Submodule K E ↦ Q ⊓ P) hplanes).trans hed)
  have hsub : Finset.univ.image j ⊆ out.erase i := by
    intro k hk
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hk
    exact hjout c
  have hbudget := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hjinj, Finset.card_univ,
    Fintype.card_fin, Finset.card_erase_of_mem hiout] at hbudget
  omega

/-- Критическая восьмииндексная версия: богатая плоскость или два
тройных блока на центр, без девятиточечной редукции. -/
theorem not_five_three_ray_covers_of_card_eight
    (μ : I → E) (hp : Pairwise fun i j ↦ LinearIndependent K ![μ i, μ j])
    (hE : finrank K E = 3) (s : Finset I) (hs : s.card = 8)
    (C : Fin 5 → Submodule K E) (hC : Function.Injective C)
    (H : ∀ c, ThreeRayCover μ s (C c)) : False := by
  classical
  by_cases hrich : ∃ P : Submodule K E, finrank K P = 2 ∧
      4 ≤ (s.filter fun i ↦ μ i ∈ P).card
  · obtain ⟨P, hP, hrich⟩ := hrich
    exact not_five_three_ray_covers_of_rich_plane μ hp hE s C hC H P hP hrich
  apply not_five_three_ray_covers_of_card_eight_of_plane_bound μ hp hE s hs C hC H
  intro P hP
  have hn : ¬ 4 ≤ (s.filter fun i ↦ μ i ∈ P).card := fun h ↦ hrich ⟨P, hP, h⟩
  omega

/-- Если каждый активный луч содержит ≥3 точек, удаление любой одной
точки сохраняет сертификат центра. -/
def ThreeRayCover.erase
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C)
    (hactive : ∀ a, 3 ≤ (s.filter fun i ↦ μ i ∈ H.ray a ∧ μ i ∉ C).card)
    (i : I) : ThreeRayCover μ (s.erase i) C where
  finrank_center := H.finrank_center
  ray := H.ray
  finrank_ray := H.finrank_ray
  ray_injective := H.ray_injective
  center_le_ray := H.center_le_ray
  cover := fun j hj ↦ H.cover j (Finset.mem_erase.mp hj).2
  active := by
    intro a
    rw [Finset.filter_erase]
    have hl := Finset.pred_card_le_card_erase
      (s := s.filter fun j ↦ μ j ∈ H.ray a ∧ μ j ∉ C) (a := i)
    have ha := hactive a
    omega

/-- После удаления одного индекса можно распределить шесть выбранных
индексов по трём разным лучам как3+2+1; во втором и третьем центре нет. -/
theorem ThreeRayCover.select_three_two_one_after_erase
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C) (hE : finrank K E = 3) (hs : 8 ≤ s.card) (j : I) :
    ∃ a b c : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      3 ≤ ((s.erase j).filter fun i ↦ μ i ∈ H.ray a).card ∧
      2 ≤ ((s.erase j).filter fun i ↦ μ i ∈ H.ray b ∧ μ i ∉ C).card ∧
      1 ≤ ((s.erase j).filter fun i ↦ μ i ∈ H.ray c ∧ μ i ∉ C).card := by
  classical
  have herase := Finset.pred_card_le_card_erase (s := s) (a := j)
  have hex : ∃ a, 3 ≤ ((s.erase j).filter fun i ↦ μ i ∈ H.ray a).card := by
    by_contra hn
    have ht (a : Fin 3) : ((s.erase j).filter fun i ↦ μ i ∈ H.ray a).card ≤ 2 := by
      have h : ¬ 3 ≤ ((s.erase j).filter fun i ↦ μ i ∈ H.ray a).card :=
        fun ha ↦ hn ⟨a, ha⟩
      omega
    have hb : (s.erase j).card ≤ 6 := calc
      _ ≤ ∑ a : Fin 3, ((s.erase j).filter fun i ↦ μ i ∈ H.ray a).card :=
        card_le_sum_cards_of_cover _ _ (fun i hi ↦
          let ⟨a, ha⟩ := H.cover i (Finset.mem_erase.mp hi).2
          ⟨a, Finset.mem_filter.mpr ⟨hi, ha⟩⟩)
      _ ≤ ∑ _a : Fin 3, 2 := Finset.sum_le_sum (fun a _ ↦ ht a)
      _ = 6 := by simp
    omega
  obtain ⟨a, ha⟩ := hex
  let T (b : Fin 3) := s.filter fun i ↦ μ i ∈ H.ray b ∧ μ i ∉ C
  have hb : ∃ b, b ≠ a ∧ j ∉ T b := by
    by_cases h0 : j ∈ T (a.succAbove 0)
    · refine ⟨a.succAbove 1, Fin.succAbove_ne _ _, ?_⟩
      intro h1
      obtain ⟨_, hj0, hjC⟩ := Finset.mem_filter.mp h0
      obtain ⟨_, hj1, _⟩ := Finset.mem_filter.mp h1
      have he := H.active_ray_unique hE hj0 hj1 hjC
      have hf := Fin.succAbove_right_injective he
      exact (by decide : (0 : Fin 2) ≠ 1) hf
    · exact ⟨a.succAbove 0, Fin.succAbove_ne _ _, h0⟩
  obtain ⟨b, hba, hjb⟩ := hb
  obtain ⟨c, hca, hcb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by decide)
  refine ⟨a, b, c, hba.symm, hca.symm, hcb.symm, ha, ?_, ?_⟩
  · rw [Finset.filter_erase]
    change 2 ≤ ((T b).erase j).card
    rw [Finset.erase_eq_of_notMem hjb]
    exact H.active b
  · rw [Finset.filter_erase]
    have hl := Finset.pred_card_le_card_erase (s := T c) (a := j)
    have hc := H.active c
    change 2 ≤ (T c).card at hc
    change 1 ≤ ((T c).erase j).card
    omega

/-- Конечный сертификат для ν: три разных индекса первого луча,
два второго и один третьего, все после удаления заданного индекса. -/
theorem ThreeRayCover.select_indices_three_two_one_after_erase
    {μ : I → E} {s : Finset I} {C : Submodule K E}
    (H : ThreeRayCover μ s C) (hE : finrank K E = 3) (hs : 8 ≤ s.card) (j : I) :
    ∃ a b c : Fin 3, ∃ x : Fin 3 ↪ I, ∃ y : Fin 2 ↪ I, ∃ z : I,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (∀ k, x k ∈ s.erase j ∧ μ (x k) ∈ H.ray a) ∧
      (∀ k, y k ∈ s.erase j ∧ μ (y k) ∈ H.ray b ∧ μ (y k) ∉ C) ∧
      z ∈ s.erase j ∧ μ z ∈ H.ray c ∧ μ z ∉ C := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ :=
    H.select_three_two_one_after_erase hE hs j
  obtain ⟨x, hx⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := (s.erase j).filter fun i ↦ μ i ∈ H.ray a) (by simpa using ha)
  obtain ⟨y, hy⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 2) (s := (s.erase j).filter fun i ↦ μ i ∈ H.ray b ∧ μ i ∉ C) (by simpa using hb)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
    0 < ((s.erase j).filter fun i ↦ μ i ∈ H.ray c ∧ μ i ∉ C).card)
  refine ⟨a, b, c, x, y, z, hab, hac, hbc, ?_, ?_, ?_⟩
  · intro k
    exact Finset.mem_filter.mp (hx ⟨k, rfl⟩)
  · intro k
    exact Finset.mem_filter.mp (hy ⟨k, rfl⟩)
  · exact Finset.mem_filter.mp hz

end MMRank
