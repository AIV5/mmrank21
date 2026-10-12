module

public import MMRank.FixedColumnSpace

@[expose] public section

/-! # Тесты в фиксированном столбцовом пространстве и транспонирование -/

namespace MMRank
open Matrix Module
variable {K P Q S : Type*} [Field K]

/-- Существует матрица с любым заданным значением на ненулевом столбце. -/
theorem exists_mulVec_eq [Fintype P] (p : P → K) (hp : p ≠ 0) (y : Q → K) :
    ∃ A : Matrix Q P K, A *ᵥ p = y := by
  obtain ⟨B, hB⟩ := exists_vecMul_eq p hp y
  exact ⟨B.transpose, by simpa only [mulVec_transpose] using hB⟩

/-- Если все правые произведения C лежат в p⊗K^Q, то и C лежит
в p⊗K^S. Нужен только один индекс Q, квадратность не требуется. -/
theorem mem_fixedColumnSpace_of_mul_mem [Fintype S] [Nonempty Q]
    (p : P → K) (C : Matrix P S K)
    (h : ∀ B : Matrix S Q K, C * B ∈ fixedColumnSpace (Q := Q) p) :
    C ∈ fixedColumnSpace (Q := S) p := by
  classical
  let q₀ : Q := Classical.arbitrary Q
  choose r hr using fun s : S ↦ h (Matrix.single s q₀ 1)
  refine ⟨fun s ↦ r s q₀, ?_⟩
  ext a s
  have hh := congrFun (congrFun (hr s) a) q₀
  simpa [vecMulVec] using hh

/-- Транспонирование фиксированного первого фактора превращает его
в ограничение образа одной прямой. Работает и при p=0. -/
theorem transpose_mem_matricesInto_span_iff [Fintype P] [Fintype Q]
    (p : P → K) (A : Matrix P Q K) :
    A.transpose ∈ matricesInto (S := Q) (Submodule.span K {p}) ↔
      A ∈ fixedColumnSpace (Q := Q) p := by
  classical
  constructor
  · rintro ⟨b, hb⟩
    have hq (q : Q) : ∃ c : K, A.transpose q = c • p := by
      have hh := (b q).property
      rw [Submodule.mem_span_singleton] at hh
      obtain ⟨c, hc⟩ := hh
      exact ⟨c, (congrFun hb q).symm.trans hc.symm⟩
    choose c hc using hq
    refine ⟨c, ?_⟩
    ext a q
    have hh := congrFun (hc q) a
    simpa [vecMulVec, mul_comm] using hh.symm
  · rintro ⟨q, rfl⟩
    refine ⟨fun j ↦ ⟨q j • p, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)⟩, ?_⟩
    ext j a
    change q j * p a = p a * q j
    exact mul_comm _ _

end MMRank
