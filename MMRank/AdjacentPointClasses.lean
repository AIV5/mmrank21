import MMRank.MinimalTestBasis

/-! # Согласование двух соседних классов минимального теста -/

namespace MMRank.ExactAlgorithm
open Matrix Module
variable {K P Q S I : Type*} [Field K]
  [Fintype P] [Fintype Q] [Fintype S] [Fintype I]

/-- На минимальном носителе все соседние Vᵢ имеют образ в Ks.
Произвольные размеры и поле; нормировка не требуется. -/
theorem V_mem_row_class_of_minimal_support (alg : ExactAlgorithm K P Q S I)
    (G : Set I) (p : P → K) (hp : p ≠ 0) (s : S → K) (hs : s ≠ 0)
    (hG : ∀ i ∉ G, alg.toCoefficients.gamma (vecMulVec p s) i = 0)
    (hc : G.ncard = Fintype.card Q) (i : G) :
    alg.V i.val ∈ matricesInto (S := Q) (Submodule.span K {s}) := by
  classical
  obtain ⟨b, hb⟩ := alg.exists_basis_of_minimal_gamma_support G p hp s hs hG hc
  have hw := alg.gamma_ne_zero_of_test_basis G p hp s hs hG b hb i
  apply (Submodule.smul_mem_iff _ hw).mp
  rw [alg.weighted_V_of_test_basis G p hp s hG b hb i]
  exact ⟨fun q ↦ ⟨b.repr (Pi.single q 1) i • s,
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)⟩, rfl⟩

end MMRank.ExactAlgorithm
