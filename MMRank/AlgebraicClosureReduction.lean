import MMRank.BaseChange
import MMRank.NormalizedHyperplane
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Нормированная редукция над алгебраическим замыканием

Переносится только алгоритм. Гиперплоскость, NZ и кондукторы выбираются
заново над новым полем. Спуск выбранной гиперплоскости не требуется.
-/

namespace MMRank.ExactAlgorithm
variable {K L P Q S ι : Type*} [Field K] [Field L]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]
  [Nonempty P] [Nonempty Q] [Nonempty S]

/-- Довести длину над K, перенести в бесконечное L, затем выбрать общую
гиперплоскость и нормировку над L. -/
theorem exists_normalized_hyperplane_map [Infinite L]
    (alg : ExactAlgorithm K P Q S ι) (f : K →+* L)
    (hdim : 1 < Fintype.card P * Fintype.card Q) (hq : 2 ≤ Fintype.card Q)
    (n : ℕ) (hn : Fintype.card ι ≤ n) :
    ∃ e : ExactAlgorithm L P Q S (Fin n), Nonempty (NormalizedHyperplaneCore e) := by
  obtain ⟨e, he⟩ := alg.exists_nonzero_length_map f hdim n hn
  obtain ⟨u, hu⟩ := e.exists_normalized_hyperplane_core he hq
  exact ⟨e.rescale u, hu⟩

/-- Явное алгебраическое замыкание удовлетворяет всем условиям редукции.
Поле K может быть конечным; характеристика не меняется. -/
theorem exists_normalized_hyperplane_algClosure
    (alg : ExactAlgorithm K P Q S ι)
    (hdim : 1 < Fintype.card P * Fintype.card Q) (hq : 2 ≤ Fintype.card Q)
    (n : ℕ) (hn : Fintype.card ι ≤ n) :
    ∃ e : ExactAlgorithm (AlgebraicClosure K) P Q S (Fin n),
      Nonempty (NormalizedHyperplaneCore e) :=
  alg.exists_normalized_hyperplane_map (algebraMap K (AlgebraicClosure K)) hdim hq n hn

/-- Общий принцип переноса запрета нормированных алгоритмов длины n
над замыканием к нижней границе n+1 над исходным полем.
Сам запрет является явной предпосылкой, а не доказанным здесь фактом. -/
theorem length_gt_of_no_normalized_algClosure
    (alg : ExactAlgorithm K P Q S ι)
    (hdim : 1 < Fintype.card P * Fintype.card Q) (hq : 2 ≤ Fintype.card Q)
    (n : ℕ)
    (hno : ∀ e : ExactAlgorithm (AlgebraicClosure K) P Q S (Fin n),
      NormalizedHyperplaneCore e → False) : n < Fintype.card ι := by
  by_contra! h
  obtain ⟨e, ⟨he⟩⟩ := alg.exists_normalized_hyperplane_algClosure hdim hq n h
  exact hno e he

end MMRank.ExactAlgorithm
