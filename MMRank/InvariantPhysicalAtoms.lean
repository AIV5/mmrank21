module

public import MMRank.InvariantPointSpan
public import MMRank.PhysicalAtomFamilies

@[expose] public section

/-! # Физические атомы инвариантного подпространства

Число атомов произвольно. Нулевой рост всего кондуктора не требуется:
достаточно инвариантного подпространства внутри im γ.
-/
namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Независимые точечные слова сразу дают атомы.
Не требуется предварительно классифицировать все активные компоненты.
Общность столбцового ядра дана явно; бесконечность поля для выбора атомов не нужна. -/
theorem exists_physical_atoms_of_invariant (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3)
    (hl : Fintype.card I ≤ 20) (η : Q → K) (hη : η ≠ 0)
    (hcol : MatrixColumnGeneric alg.U η)
    (h1 : (1 : I → K) ∈ alg.toCoefficients.alphaOn (coordinateHyperplane η))
    (L : Submodule K (I → K)) (hL : L ≤ alg.toCoefficients.gamma.range)
    (hstable : alg.toCoefficients.alphaOn (coordinateHyperplane η) * L = L)
    (n : ℕ) (hn : n ≤ finrank K L) :
    ∃ a : Fin n → PhysicalAtom alg,
      Function.Injective (fun j ↦ (a j).support) ∧
      ∀ j, alg.toCoefficients.gamma (a j).test ∈ L := by
  obtain ⟨w, hw, hi⟩ := exists_linearIndependent_pointWords_of_invariant _ L h1 hstable n hn
  have ha (j) : ∃ a : PhysicalAtom alg, alg.toCoefficients.gamma a.test = w j := by
    obtain ⟨C, hC⟩ := hL (hw j).1
    obtain ⟨a, ha⟩ := PhysicalAtom.exists_of_pointTest_column_generic hp hq hs hl η hη hcol h1 C
      (by simpa only [hC] using (hw j).2)
    exact ⟨a, by rw [ha, hC]⟩
  choose a ha using ha
  refine ⟨a, ?_, fun j ↦ (ha j).symm ▸ (hw j).1⟩
  intro j k he
  change (a j).support = (a k).support at he
  have hnz : w j ≠ 0 := hi.ne_zero j
  obtain ⟨i, hwi⟩ : ∃ i, w j i ≠ 0 := by simpa [funext_iff] using hnz
  have hj : i ∈ (a j).support := by change alg.toCoefficients.gamma (a j).test i ≠ 0; rwa [ha]
  obtain ⟨c, _, htest⟩ := (a j).test_smul_of_common_index (a k) hj (by rwa [← he])
  have hwords : w k = c • w j := by rw [← ha k, htest, map_smul, ha]
  exact (hi.eq_of_smul_apply_eq_smul_apply 1 c k j one_ne_zero (by simpa using hwords)).symm

end MMRank.ExactAlgorithm
