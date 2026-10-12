module

public import MMRank.BaseChange
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

/-!
# Явное бесконечное расширение для подготовительной редукции

Поле рациональных функций K(t) бесконечно даже при конечном K.
Сначала длина нормируется над K, затем данный алгоритм переносится в K(t).
Это не утверждение о сохранении минимальной билинейной сложности.
-/

namespace MMRank

/-- Поле рациональных функций над любой областью целостности бесконечно. -/
theorem ratFunc_infinite (K : Type*) [CommRing K] [IsDomain K] : Infinite (RatFunc K) :=
  Infinite.of_injective (algebraMap (Polynomial K) (RatFunc K)) (RatFunc.algebraMap_injective K)

namespace ExactAlgorithm

variable {K P Q S ι : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]
  [Nonempty P] [Nonempty Q] [Nonempty S]

/-- Нормированная длина с ненулевыми коэффициентами над явным бесконечным расширением.
Нормировка выполняется над исходным K; перенос не меняет число слагаемых. -/
theorem exists_nonzero_length_ratFunc (d : ExactAlgorithm K P Q S ι)
    (hdim : 1 < Fintype.card P * Fintype.card Q) (n : ℕ) (hn : Fintype.card ι ≤ n) :
    ∃ e : ExactAlgorithm (RatFunc K) P Q S (Fin n), e.toCoefficients.NonzeroTerms := by
  exact d.exists_nonzero_length_map (algebraMap K (RatFunc K)) hdim n hn

end ExactAlgorithm

end MMRank
