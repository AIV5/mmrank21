import MMRank.PlaneCapacity
import MMRank.SimpleHyperplaneNormalization
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Три непересекающиеся тройки первых коэффициентов с фиксированными
направлениями имеют независимые направления. Полнота классов не нужна. -/
theorem three_class_directions_linearIndependent (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (p : Fin 3 → P → K) (G : Fin 3 → Set I)
    (hd : Pairwise (fun a b ↦ Disjoint (G a) (G b))) (hc : ∀ j, (G j).ncard = 3)
    (hG : ∀ j i, i ∈ G j → alg.U i ∈ fixedColumnSpace (Q := Q) (p j)) :
    LinearIndependent K p := by
  classical
  let T := Submodule.span K (Set.range p)
  have htop : T = ⊤ := by
    by_contra hn
    obtain ⟨φ, hφ, hker⟩ := T.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hn)
    have hdim : finrank K φ.ker = 2 := by
      have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
      rw [Module.finrank_fintype_fun_eq_card, hp] at hh
      omega
    let J : Set I := ⋃ j, G j
    have hj : J.ncard = 9 := by
      rw [Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) hd]
      simp [hc, finsum_eq_sum_of_fintype]
    have hm := (alg.plane_capacity hp hq hs hl η hη h1 φ.ker hdim J (by
      intro i hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      have hu := (transpose_mem_matricesInto_span_iff (p j) (alg.U i)).mpr (hG j i hj)
      apply (mem_matricesInto φ.ker _).mpr
      apply ((mem_matricesInto _ _).mp hu).trans
      apply Submodule.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hker (Submodule.subset_span (Set.mem_range_self j)))).2.2
    omega
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact htop.ge
  · simp [Module.finrank_fintype_fun_eq_card, hp]

/-- Для нормировки достаточно ненулевых U;
полный общий пакет не нужен. Масштабирование не меняет
принадлежность коэффициентов заданным столбцовым пространствам. -/
theorem three_class_directions_linearIndependent_of_nonzero [Infinite K]
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (hn : ∀ i, alg.U i ≠ 0)
    (p : Fin 3 → P → K) (G : Fin 3 → Set I)
    (hd : Pairwise (fun a b ↦ Disjoint (G a) (G b))) (hc : ∀ j, (G j).ncard = 3)
    (hG : ∀ j i, i ∈ G j → alg.U i ∈ fixedColumnSpace (Q := Q) (p j)) :
    LinearIndependent K p := by
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨η, hη, u, h1⟩ := alg.toCoefficients.exists_rescale_one_mem_hyperplane hn
  apply (alg.rescale u).three_class_directions_linearIndependent hp hq hs hl η hη
    h1 p G hd hc
  intro j i hi
  change ((u i)⁻¹ : Kˣ) • alg.U i ∈ fixedColumnSpace (Q := Q) (p j)
  exact Submodule.smul_mem _ (((u i)⁻¹ : Kˣ) : K) (hG j i hi)

/-- Отражение даёт тот же вывод для фиксированных строковых направлений. -/
theorem three_row_directions_linearIndependent [Infinite K]
    (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (hn : ∀ i, alg.U i ≠ 0)
    (q : Fin 3 → Q → K) (G : Fin 3 → Set I)
    (hd : Pairwise (fun a b ↦ Disjoint (G a) (G b))) (hc : ∀ j, (G j).ncard = 3)
    (hG : ∀ j i, i ∈ G j → alg.U i ∈ matricesInto (S := P) (Submodule.span K {q j})) :
    LinearIndependent K q := by
  apply alg.reflect.three_class_directions_linearIndependent_of_nonzero hq hp hs hl
    (fun i ↦ by simpa only [ExactAlgorithm.reflect, Coefficients.reflect, ne_eq,
      transpose_eq_zero] using hn i) q G hd hc
  intro j i hi
  exact (transpose_mem_matricesInto_span_iff (q j) (alg.U i).transpose).mp
    (by simpa only [transpose_transpose] using hG j i hi)

end MMRank.ExactAlgorithm
