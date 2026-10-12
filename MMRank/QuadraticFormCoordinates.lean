module

public import MMRank.QuadraticThreeRay

@[expose] public section

/-! # Квадратичные формы в шести координатах, включая характеристику2
Представление не требует associated.
-/
noncomputable section
namespace MMRank
open Matrix Module
variable {K : Type*} [Field K]

/-- Любая квадратичная форма на K³ — линейная форма от шести мономов. -/
theorem exists_quadratic_coordinate_form (Q : QuadraticForm K (Fin 3 → K)) :
    ∃ φ : Dual K (Fin 6 → K), ∀ x, φ (quadraticVeronese x) = Q x := by
  let e (i : Fin 3) : Fin 3 → K := Pi.single i 1
  let c : Fin 6 → K := ![Q (e 0), QuadraticMap.polar Q (e 0) (e 1), Q (e 1),
    QuadraticMap.polar Q (e 0) (e 2), Q (e 2), QuadraticMap.polar Q (e 1) (e 2)]
  refine ⟨dotProductEquiv K (Fin 6) c, ?_⟩
  intro x
  have hx : x = x 0 • e 0 + x 1 • e 1 + x 2 • e 2 := by
    ext i; fin_cases i <;> simp [e]
  conv_rhs => rw [hx]
  rw [QuadraticMap.map_add Q (x 0 • e 0 + x 1 • e 1) (x 2 • e 2),
    QuadraticMap.map_add Q (x 0 • e 0) (x 1 • e 1)]
  simp only [Q.map_smul, Q.polar_add_left,
    Q.polar_smul_left, Q.polar_smul_right, smul_eq_mul]
  change c ⬝ᵥ quadraticVeronese x = _
  simp only [c, quadraticVeronese, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero]
  ring

end MMRank
