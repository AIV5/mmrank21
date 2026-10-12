import MMRank.LengthTwentyOneFirstRank

/-! # Безусловная нижняя21 над произвольным полем

Положительный рост запрещается одним обменом пары
в представителе с минимальной первой суммой рангов; нулевой рост
оставляет трёхатомный бюджет. Перенос в замыкание
снимает ограничения поля.
-/
namespace MMRank.ExactAlgorithm
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Каждый точный алгоритм умножения матриц3×3 имеет не менее21 слагаемого.
Поле произвольно. Минимальность, NonzeroTerms, нормировка, алгебраическая
замкнутость и граница насыщения не являются предпосылками. -/
theorem length_bound_twenty_one (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3) :
    21 ≤ Fintype.card I :=
  alg.length_bound_twenty_one_by_first_rank_descent hp hq hs

end MMRank.ExactAlgorithm
