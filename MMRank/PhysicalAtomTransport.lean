module

public import MMRank.PhysicalAtomFullClasses

@[expose] public section

/-! # Возврат физических атомов из независимо нормированных ориентаций -/
namespace MMRank.ExactAlgorithm.PhysicalAtom
open Matrix
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]
  {alg : ExactAlgorithm K P Q S I}

/-- Калибровка не меняет фиксированные физические направления атома. -/
def rescale (a : PhysicalAtom alg) (u : I → Kˣ) : PhysicalAtom (alg.rescale u) where
  first := a.first
  last := a.last
  first_ne_zero := a.first_ne_zero
  last_ne_zero := a.last_ne_zero
  card_support := by rw [alg.gamma_rescale_support u]; exact a.card_support

end MMRank.ExactAlgorithm.PhysicalAtom
