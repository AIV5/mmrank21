# Proof overview

This is a reading guide to the formal proof, not a separate complete proof
on paper. Start with [PublicTheorem.lean](../MMRank/PublicTheorem.lean) for
the advertised statement and
[LengthTwentyOneFirstRank.lean](../MMRank/LengthTwentyOneFirstRank.lean) for
the main assembly.

## Spaces used in the argument

The coefficient maps take values in the coordinate algebra K^I:

```text
alpha(A)_i = trace(U_i A)
beta(B)_i  = trace(V_i B)
gamma(C)_i = trace(W_i C).
```

After extending the field, choose a suitable hyperplane F in the middle
row space Q → K. The input A is restricted to maps vanishing on F, and B
to maps whose image lies in F. Their coefficient images are M and B_F;
N is the full image of gamma. In the 3 × 3 case their dimensions are 3, 6
and 9, respectively. Rescaling the coefficients gives a normalization with
the constant coordinate vector 1 in M.

For subspaces X and Y of K^I, XY denotes the linear span of their
coordinatewise products. The conductor (N:M) is the subspace of vectors x
such that mx belongs to N for every m in M. It is not a quotient space.
The proof uses

```text
D = (N:M),    E = MD,    Z = (B_F:M),
d = dim D,   e = dim E,  z = dim Z.
```

The growth is e − d. A physical atom is a nonzero rank-one test C whose
coordinate vector gamma(C) has the minimum support size, three in this
format. Exactness then gives the associated factorization of the U and V
coefficients on those three indices. These definitions are in
[RestrictedCoefficients](../MMRank/RestrictedCoefficients.lean),
[Conductor](../MMRank/Conductor.lean) and
[PhysicalAtom](../MMRank/PhysicalAtom.lean).

## Argument

1. **Reduce to length 20 over an algebraic closure.** Relabeling, padding and
   extension of scalars preserve exactness. An independently proved lower
   bound of 20 excludes zero terms; it does not use the theorem of 21.
   See [AlgebraicClosureReduction](../MMRank/AlgebraicClosureReduction.lean),
   [LengthReduction](../MMRank/LengthReduction.lean) and
   [LengthTwenty](../MMRank/LengthTwenty.lean).

2. **Minimize the first rank sum.** Choose a representative minimizing
   the sum of ranks of its U coefficients. This natural-number minimum is
   selected inside the proof, not assumed of the input algorithm.
   See [RankSumMinimality](../MMRank/RankSumMinimality.lean).

3. **Normalize and bound the conductor dimensions.** The coordinate test
   space M and its conductor D satisfy 3 ≤ dim(D) ≤ dim(MD) ≤ 5, with further
   bounds restricting growth to zero or one. The normalization needs generic
   column cores. See
   [CriticalConductorDimensionsDirect](../MMRank/CriticalConductorDimensionsDirect.lean).

4. **Exclude positive growth by one pair exchange.** A regular supported
   slice and its unique coefficient relation yield a pair with first factor
   of rank at most one in the span of the original pairs. Replacing a pair
   with first rank at least two strictly decreases the first rank sum.
   See [FirstRankGrowthExclusion](../MMRank/FirstRankGrowthExclusion.lean),
   [RegularPencilGrowth](../MMRank/RegularPencilGrowth.lean),
   [ResolventPairDescent](../MMRank/ResolventPairDescent.lean) and
   [OnePairRankDescent](../MMRank/OnePairRankDescent.lean).

5. **Exclude four physical atoms.** Zero growth gives physical atoms,
   groups of terms attached to simple test directions. If dim(D) ≥ 4,
   choose four of them. They occupy twelve of the twenty indices, leaving
   eight terms to reconstruct a five-dimensional annihilator. The
   all-field reconstruction obstruction rules this out. See
   [ZeroGrowthPhysicalAtoms](../MMRank/ZeroGrowthPhysicalAtoms.lean) and
   [FourAtomResidualExclusion](../MMRank/FourAtomResidualExclusion.lean).

6. **Finish with three atoms.** Now dim(D) = 3. For second-conductor
   dimension z, the dimension budget at length at most 20 gives z ≥ 2.
   Three compatible diagonal tests give length at least 9z + 3 ≥ 21.
   See [ThreeProfileExclusion](../MMRank/ThreeProfileExclusion.lean).

These steps give `no_length_twenty_by_first_rank_descent` over an
algebraically closed field. The extension-of-scalars reduction gives
`length_bound_twenty_one_by_first_rank_descent` over the original field.
[LengthTwentyOne.lean](../MMRank/LengthTwentyOne.lean) exports the conclusion
over an arbitrary field, without a minimality or nonzero-term hypothesis.

The proof uses algebraic arguments rather than an exhaustive search over
finite-field decompositions. No externally generated numerical certificate
is an input to this repository's build.
