module

public import MMRank.CriticalConductorDimensionsDirect
public import MMRank.AlgebraicClosureReduction

@[expose] public section

/-! # Безусловная нижняя граница двадцать над произвольным полем -/

namespace MMRank.ExactAlgorithm
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- Любой точный алгоритм333 над любым полем имеет длину≥20.
При длине19 общие размерностные оценки вынуждают e=5,z=2,
но этот профиль требует длину≥21. Точечные тесты и редукция323 не нужны. -/
theorem length_bound_twenty (alg : ExactAlgorithm K P Q S I)
    (hp : Fintype.card P = 3) (hq : Fintype.card Q = 3) (hs : Fintype.card S = 3) :
    20 ≤ Fintype.card I := by
  let : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty Q := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty S := Fintype.card_pos_iff.mp (by omega)
  have hh := alg.length_gt_of_no_normalized_algClosure (by simp [hp, hq]) (by omega) 19
    (fun e h ↦ by
      have hb := e.critical_atom_dimension_bounds_direct h hp hq hs (by simp)
      have hsum := e.restricted_two_conductor_dimension_sum_bound h.F 1 (by omega)
        (by have := h.codim_one; omega) h.one_mem (by simp [hp])
      simp only [hp, hq, hs, Fintype.card_fin] at hsum
      have hlarge := hb.2.2.2.2.2
      dsimp only at hb hlarge
      omega)
  omega

end MMRank.ExactAlgorithm
