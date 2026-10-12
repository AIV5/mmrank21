import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Ранговая факторизация

Канонические отображения `f.rangeRestrict` и `f.range.subtype` уже есть в mathlib.
Здесь выделены размерностный критерий минимальности и координатная факторизация.
Общий результат требует конечномерности только образа, а не исходных пространств.
Матричная специализация использует правое действие на строках без смены конвенций.
-/

namespace MMRank

section Dimension

variable {K E F G : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup G] [Module K G]

/-- Любая факторизация через конечномерное пространство ограничивает ранг сверху. -/
theorem finrank_range_le_of_factorization [FiniteDimensional K G]
    (a : E →ₗ[K] G) (b : G →ₗ[K] F) :
    Module.finrank K (LinearMap.range (b.comp a)) ≤ Module.finrank K G := by
  calc
    Module.finrank K (LinearMap.range (b.comp a)) ≤ Module.finrank K b.range :=
      Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left a b)
        (Module.rank_lt_aleph0 K b.range)
    _ ≤ Module.finrank K G := b.finrank_range_le

end Dimension

section Matrix

variable {K P Q : Type*} [Field K] [Fintype P] [Fintype Q]

/-- Обычный ранг матрицы совпадает с размерностью образа её действия на строки. -/
theorem matrix_rank_eq_finrank_rowRange (U : Matrix P Q K) :
    U.rank = Module.finrank K U.vecMulLinear.range := by
  rw [← Matrix.mulVecLin_transpose, ← Matrix.rank, Matrix.rank_transpose]

/-- В конечных размерах над полем ранг равен нулю ровно у нулевой матрицы. -/
theorem matrix_rank_eq_zero_iff (U : Matrix P Q K) : U.rank = 0 ↔ U = 0 := by
  classical
  rw [matrix_rank_eq_finrank_rowRange, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  change LinearMap.toMatrixRight'.symm U = 0 ↔ U = 0
  exact LinearEquiv.map_eq_zero_iff _

end Matrix

end MMRank
