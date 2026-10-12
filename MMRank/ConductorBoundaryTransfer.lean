module

public import MMRank.ConductorGrowth

@[expose] public section

/-! # Перенос кондукторной границы между вложенными пространствами

Общая конструкция использует линейное семейство операторов с единичным оператором,
не предполагая коммутативности или полупростоты. Координатное умножение — следствие.
-/

namespace MMRank

open Module

section Action

variable {R P V : Type*} [CommRing R]
variable [AddCommGroup P] [Module R P] [AddCommGroup V] [Module R V]

/-- Кондуктор для произвольного линейного семейства операторов.
Коммутирование операторов и замкнутость семейства по композиции не нужны. -/
def actionConductor (b : P →ₗ[R] V →ₗ[R] V) (T : Submodule R V) : Submodule R V :=
  ⨅ a : P, T.comap (b a)

@[simp] theorem mem_actionConductor (b : P →ₗ[R] V →ₗ[R] V) (T : Submodule R V) (v : V) :
    v ∈ actionConductor b T ↔ ∀ a, b a v ∈ T := by
  simp [actionConductor]

/-- Действие на кондукторе с пространством значений T. -/
def actionOnConductor (b : P →ₗ[R] V →ₗ[R] V) (T : Submodule R V) :
    P →ₗ[R] actionConductor b T →ₗ[R] T where
  toFun a :=
    { toFun v := ⟨b a v.val, (mem_actionConductor b T v.val).mp v.property a⟩
      map_add' x y := by apply Subtype.ext; exact (b a).map_add _ _
      map_smul' r x := by apply Subtype.ext; exact (b a).map_smul _ _ }
  map_add' a a' := by ext v; exact congrArg (fun f : V →ₗ[R] V ↦ f v.val) (b.map_add a a')
  map_smul' r a := by ext v; exact congrArg (fun f : V →ₗ[R] V ↦ f v.val) (b.map_smul r a)

/-- θ(v)(a)=b(a)(v) mod S в факторе T/(S∩T).
Для S≤T это именно T/S. -/
def conductorTransferMap (b : P →ₗ[R] V →ₗ[R] V) (S T : Submodule R V) :
    actionConductor b T →ₗ[R] P →ₗ[R] (T ⧸ S.comap T.subtype) :=
  ((actionOnConductor b T).compr₂ (S.comap T.subtype).mkQ).flip

@[simp] theorem conductorTransferMap_apply (b : P →ₗ[R] V →ₗ[R] V)
    (S T : Submodule R V) (v : actionConductor b T) (a : P) :
    conductorTransferMap b S T v a = Submodule.Quotient.mk (actionOnConductor b T a v) := rfl

end Action

section Dimension

variable {K P V : Type*} [Field K]
variable [AddCommGroup P] [Module K P] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K P] [FiniteDimensional K V]

end Dimension

section Multiplication

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Линейное семейство левых умножений элементами M.
В правой записи сначала применяется вектор, затем соответствующий оператор. -/
def multiplierAction (M : Submodule R A) : M →ₗ[R] A →ₗ[R] A :=
  (LinearMap.mul R A).comp M.subtype

@[simp] theorem multiplierAction_apply (M : Submodule R A) (m : M) (v : A) :
    multiplierAction M m v = m.val * v := rfl

end Multiplication

section Commutative

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

end Commutative

section AlgebraDimension

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]

end AlgebraDimension

end MMRank
