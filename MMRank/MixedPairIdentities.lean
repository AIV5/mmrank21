import MMRank.LocalPairReplacement

namespace MMRank
open Matrix
variable {K P Q S I : Type*}
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Полная простая пара линейна по каждой из двух коэффициентных матриц. -/
def matrixCoefficientPairBilin [CommSemiring K] : Matrix P Q K →ₗ[K] Matrix Q S K →ₗ[K]
    (Matrix Q P K →ₗ[K] Matrix S Q K →ₗ[K] K) :=
  LinearMap.mk₂ K matrixCoefficientPair
    (by intro U U' V; ext A B; simp [matrixCoefficientPair, Matrix.add_mul, add_mul])
    (by intro c U V; ext A B; simp [matrixCoefficientPair, mul_assoc])
    (by intro U V V'; ext A B; simp [matrixCoefficientPair, Matrix.add_mul, mul_add])
    (by intro c U V; ext A B; simp [matrixCoefficientPair, mul_left_comm])

variable [Field K]

open scoped Classical

end MMRank
