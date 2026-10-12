module

public import MMRank.RankOneHyperplanes
public import Mathlib.GroupTheory.CosetCover

@[expose] public section

/-! # Матричное фактор-тождество с одним лишним членом

U имеет размер p×q, V — q×s;
V не переименовывается в транспонированную матрицу. Левое ядро U относится
к действию на столбцы, второе ядро — к правому действию V на строки.
-/

set_option backward.isDefEq.respectTransparency false

namespace MMRank
open Matrix Module
open scoped BigOperators

variable {K P Q S L I : Type*} [Field K] [Fintype P] [Fintype Q] [Fintype S]
  [AddCommGroup L] [Module K L]

/-- Двустороннее умножение с физическими размерами коэффициентов. -/
def matrixSandwich (U : Matrix P Q K) (V : Matrix Q S K) :
    Matrix Q Q K →ₗ[K] Matrix P S K :=
  (mulRightLinearMap P K V).comp (mulLeftLinearMap Q K U)

omit [Fintype P] [Fintype S] in
@[simp] theorem matrixSandwich_apply (U : Matrix P Q K) (V : Matrix Q S K)
    (X : Matrix Q Q K) : matrixSandwich U V X = U * X * V := rfl

end MMRank
