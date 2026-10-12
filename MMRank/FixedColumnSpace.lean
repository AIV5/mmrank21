module

public import MMRank.PhysicalConductor

@[expose] public section

/-! # Пространство матриц с фиксированным первым внешним фактором -/

namespace MMRank
open Matrix Module
variable {K P Q S : Type*} [Field K]

/-- Прямоугольный аналог минимального правого идеала: все p⊗q. -/
def fixedColumnSpace (p : P → K) : Submodule K (Matrix P Q K) :=
  (vecMulVecBilin K K p).range

theorem fixedColumnMap_injective {p : P → K} (hp : p ≠ 0) :
    Function.Injective (vecMulVecBilin K K p : (Q → K) →ₗ[K] Matrix P Q K) := by
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by simpa [funext_iff] using hp
  intro v w h
  ext k
  exact mul_left_cancel₀ hj (congrFun (congrFun h j) k)

theorem finrank_fixedColumnSpace [Fintype Q] {p : P → K} (hp : p ≠ 0) :
    finrank K (fixedColumnSpace (Q := Q) p) = Fintype.card Q := by
  rw [fixedColumnSpace, LinearMap.finrank_range_of_inj (fixedColumnMap_injective hp)]
  simp

/-- Ненулевая строка достигает любого целевого значения умножением справа. -/
theorem exists_vecMul_eq [Fintype S] (s : S → K) (hs : s ≠ 0) (q : Q → K) :
    ∃ B : Matrix S Q K, s ᵥ* B = q := by
  obtain ⟨v, hv⟩ := exists_dotProduct_eq_one s hs
  exact ⟨vecMulVec v q, by rw [vecMul_vecMulVec, dotProduct_comm, hv, one_smul]⟩

/-- Ненулевая простая матрица порождает всё пространство с тем же
первым фактором умножениями справа. -/
theorem fixedColumnSpace_eq_range_mul [Fintype S] (p : P → K)
    (s : S → K) (hs : s ≠ 0) :
    fixedColumnSpace (Q := Q) p =
      (mulLeftLinearMap Q K (vecMulVec p s)).range := by
  ext A
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨B, hB⟩ := exists_vecMul_eq s hs q
    exact ⟨B, by simp only [mulLeftLinearMap_apply, vecMulVec_mul, hB]; rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨s ᵥ* B, (vecMulVec_mul p s B).symm⟩

end MMRank
