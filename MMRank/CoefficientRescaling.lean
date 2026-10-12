import MMRank.RestrictedSupport

/-!
# Компенсированное изменение масштаба коэффициентов

U'_i = u_i⁻¹ U_i, V'_i = V_i, W'_i = u_i W_i для обратимых скаляров u_i.
Каждое слагаемое точной формулы сохраняется. Это не замена базисов физических
пространств; она определена уже над коммутативным полукольцом.
-/

namespace MMRank

open Matrix Module

variable {K P Q S ι : Type*}

section Semiring

variable [CommSemiring K]

/-- Поточечное умножение на обратимые скаляры как линейный эквивалент. -/
def coordinateScale (u : ι → Kˣ) : (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.piCongrRight (fun i ↦ (u i).mulLeftLinearEquiv K K)

@[simp] theorem coordinateScale_apply (u : ι → Kˣ) (a : ι → K) (i : ι) :
    coordinateScale u a i = (u i : K) * a i := rfl

@[simp] theorem coordinateScale_symm_apply (u : ι → Kˣ) (a : ι → K) (i : ι) :
    (coordinateScale u).symm a i = ((u i)⁻¹ : Kˣ) * a i := rfl

@[simp] theorem coordinateScale_inv (u : ι → Kˣ) :
    coordinateScale (fun i ↦ (u i)⁻¹) = (coordinateScale u).symm := rfl

/-- Масштабирование первого множителя коммутирует с поточечным умножением. -/
theorem coordinateScale_mul (u : ι → Kˣ) (a b : ι → K) :
    coordinateScale u a * b = coordinateScale u (a * b) := by
  ext i
  exact mul_assoc _ _ _

/-- Изменение масштаба не меняет координатный носитель произвольного подмодуля. -/
theorem coordinateScale_support_iff (u : ι → Kˣ) (M : Submodule K (ι → K)) (i : ι) :
    (∃ a ∈ M.map (coordinateScale u).toLinearMap, a i ≠ 0) ↔
      ∃ a ∈ M, a i ≠ 0 := by
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hn⟩
    exact ⟨a, ha, fun hz ↦ hn (by simp [hz])⟩
  · rintro ⟨a, ha, hn⟩
    refine ⟨coordinateScale u a, ⟨a, ha, rfl⟩, ?_⟩
    intro hz
    apply hn
    have h := congrArg (fun x : K ↦ ((u i)⁻¹ : Kˣ) * x) hz
    simpa [mul_assoc] using h

/-- Отсутствие делителей нуля в любой паре подмодулей сохраняется в обе стороны. -/
theorem coordinateScale_no_zero_divisors_iff (u : ι → Kˣ) (M N : Submodule K (ι → K)) :
    (∀ a ∈ M.map (coordinateScale u).toLinearMap, ∀ b ∈ N, a * b = 0 → a = 0 ∨ b = 0) ↔
      (∀ a ∈ M, ∀ b ∈ N, a * b = 0 → a = 0 ∨ b = 0) := by
  constructor
  · intro h a ha b hb hab
    have hz : coordinateScale u a * b = 0 := by rw [coordinateScale_mul, hab, map_zero]
    rcases h _ ⟨a, ha, rfl⟩ b hb hz with hzero | hzero
    · exact Or.inl ((coordinateScale u).map_eq_zero_iff.mp hzero)
    · exact Or.inr hzero
  · intro h _ ha b hb hab
    obtain ⟨a, ha, rfl⟩ := ha
    have hz : a * b = 0 := (coordinateScale u).map_eq_zero_iff.mp
      (by rwa [← coordinateScale_mul])
    rcases h a ha b hb hz with hzero | hzero
    · left; simp [hzero]
    · exact Or.inr hzero

namespace Coefficients

/-- Компенсированное изменение первого и третьего коэффициентов. -/
def rescale (d : Coefficients K P Q S ι) (u : ι → Kˣ) : Coefficients K P Q S ι where
  U i := ((u i)⁻¹ : Kˣ) • d.U i
  V := d.V
  W i := (u i) • d.W i

variable [Fintype P] [Fintype Q] [Fintype S]

omit [Fintype S] in
theorem alpha_rescale (d : Coefficients K P Q S ι) (u : ι → Kˣ) :
    (d.rescale u).alpha = (coordinateScale u).symm.toLinearMap.comp d.alpha := by
  ext A i
  simp [alpha, traceCoordinates, rescale, Units.smul_def, Matrix.smul_mul]

omit [Fintype Q] in
theorem gamma_rescale (d : Coefficients K P Q S ι) (u : ι → Kˣ) :
    (d.rescale u).gamma = (coordinateScale u).toLinearMap.comp d.gamma := by
  ext C i
  simp [gamma, traceCoordinates, rescale, Units.smul_def, Matrix.smul_mul]

omit [Fintype S] in
theorem alphaOn_rescale (d : Coefficients K P Q S ι) (u : ι → Kˣ)
    (F : Submodule K (Q → K)) :
    (d.rescale u).alphaOn F = (d.alphaOn F).map (coordinateScale u).symm.toLinearMap := by
  rw [alphaOn, alpha_rescale, Submodule.map_comp]
  rfl

omit [Fintype Q] in
theorem range_gamma_rescale (d : Coefficients K P Q S ι) (u : ι → Kˣ) :
    (d.rescale u).gamma.range = d.gamma.range.map (coordinateScale u).toLinearMap := by
  rw [gamma_rescale, LinearMap.range_comp]

omit [Fintype S] in
/-- Если функция масштабов лежала в A_F, после нормировки A_F содержит единицу. -/
theorem one_mem_alphaOn_rescale (d : Coefficients K P Q S ι) (u : ι → Kˣ)
    (F : Submodule K (Q → K)) (hu : (fun i ↦ (u i : K)) ∈ d.alphaOn F) :
    1 ∈ (d.rescale u).alphaOn F := by
  rw [alphaOn_rescale]
  refine ⟨_, hu, ?_⟩
  ext i
  simp

end Coefficients

namespace ExactAlgorithm

variable [Fintype P] [Fintype Q] [Fintype S] [Fintype ι]

/-- Компенсированное изменение масштаба сохраняет точность и множество слагаемых. -/
def rescale (d : ExactAlgorithm K P Q S ι) (u : ι → Kˣ) : ExactAlgorithm K P Q S ι where
  toCoefficients := d.toCoefficients.rescale u
  exact_formula A B := by
    rw [d.exact_formula]
    apply Finset.sum_congr rfl
    intro i _
    simp [Coefficients.rescale, Units.smul_def, Matrix.smul_mul, smul_smul,
      mul_comm, mul_assoc]

/-- Обратная калибровка возвращает исходный точный алгоритм.
Размеры произвольны; достаточно коммутативного полукольца. -/
@[simp] theorem rescale_inverse (alg : ExactAlgorithm K P Q S ι) (u : ι → Kˣ) :
    (alg.rescale u).rescale (fun i ↦ (u i)⁻¹) = alg := by
  cases alg with
  | mk d he =>
    cases d
    simp [rescale, Coefficients.rescale, smul_smul]

/-- Ненулевые матричные коэффициенты остаются ненулевыми. -/
theorem nonzeroTerms_rescale (d : ExactAlgorithm K P Q S ι) (u : ι → Kˣ)
    (hd : d.toCoefficients.NonzeroTerms) : (d.rescale u).toCoefficients.NonzeroTerms := by
  intro i
  refine ⟨?_, (hd i).2.1, ?_⟩
  · intro h
    have he := congrArg (fun M : Matrix P Q K ↦ u i • M) h
    exact (hd i).1 (by simpa [rescale, Coefficients.rescale, smul_smul] using he)
  · intro h
    have he := congrArg (fun M : Matrix S P K ↦ (u i)⁻¹ • M) h
    exact (hd i).2.2 (by simpa [rescale, Coefficients.rescale, smul_smul] using he)

end ExactAlgorithm

end Semiring

section Field

variable [Field K] [Infinite K] [Fintype P] [Fintype Q] [Fintype ι]

/-- Из полного носителя A_F получаем допустимые масштабы, приводящие элемент к единице.
Ни точность алгоритма, ни инъективность матрицы-прообраза не предполагаются. -/
theorem Coefficients.exists_rescale_one_mem_alphaOn (d : Coefficients K P Q S ι)
    (F : Submodule K (Q → K)) (h : ∀ i, ∃ a ∈ d.alphaOn F, a i ≠ 0) :
    ∃ u : ι → Kˣ, 1 ∈ (d.rescale u).alphaOn F := by
  obtain ⟨a, ha, hn⟩ := exists_mem_forall_ne_zero (d.alphaOn F) h
  exact ⟨fun i ↦ Units.mk0 (a i) (hn i), d.one_mem_alphaOn_rescale _ F ha⟩

end Field

end MMRank
