# A lower bound of 21 for 3 × 3 matrix multiplication over every field

**Andrey Ivanov**[^pronunciation] · Lean 4 formalization

This repository proves that every exact bilinear algorithm for multiplying
two 3 × 3 matrices over an arbitrary field uses at least 21 products of
input linear forms:

$$R_K\langle 3,3,3\rangle \geqslant 21 \qquad\text{for every field }K.$$

The proof is supplied in Lean. This README states the result, explains how to
check it, and provides a short route through the formal development.

## The theorem

Let $K$ be a field and $I$ a finite set. Suppose that $a_i,b_i$ are
$K$-linear forms on $\mathrm{Mat}_3(K)$ and $W_i\in\mathrm{Mat}_3(K)$,
and that, for every pair of matrices $A,B$,

$$AB=\sum_{i\in I}a_i(A)b_i(B)W_i.$$

Then $|I|\geqslant21$. The linear forms and output matrices are unrestricted.
In particular, the theorem does not assume that the algorithm is minimal,
that its terms are nonzero, or that any coefficient matrices have prescribed
ranks. It applies in every characteristic, including characteristic 2, and
to finite as well as infinite fields. It concerns exact bilinear complexity;
it makes no claim about border rank or arbitrary arithmetic circuits.

The public statement is
[`MMRank.matrix_multiplication_length_ge_twenty_one`](MMRank/PublicTheorem.lean):

```lean
theorem matrix_multiplication_length_ge_twenty_one
    {K I : Type*} [Field K] [Fintype I]
    (a b : I → (Matrix (Fin 3) (Fin 3) K →ₗ[K] K))
    (W : I → Matrix (Fin 3) (Fin 3) K)
    (h : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      A * B = ∑ i, (a i A * b i B) • W i) :
    21 ≤ Fintype.card I
```

This interface reduces the claim to the underlying theorem
[`MMRank.ExactAlgorithm.length_bound_twenty_one`](MMRank/LengthTwentyOne.lean).
The translation from linear forms to trace coefficients is itself proved in
Lean.

The formal development uses **right action on row vectors**, with coefficient
cycle **UVW** and input cycle **CBA**. Its exactness identity is
`BA = ∑ᵢ tr(UᵢA) tr(VᵢB) Wᵢ`. The public AB statement above is an equivalent
interface. [The statement guide](docs/STATEMENT.md) gives the matrix shapes
and the formal equivalence.

## Check the proof

Install [elan](https://github.com/leanprover/elan#installation), the Lean
toolchain manager, and make `lake` available on your PATH. Git and Bash are
also needed. From this repository's root, run:

```sh
lake exe cache get
./scripts/check.sh
```

The first command downloads compiled dependencies. The second builds the
proof, prints both theorem signatures and their axioms, and rejects any
project declaration whose proof uses an axiom outside `propext`, `Classical.choice` and `Quot.sound`. In particular, it rejects
`sorryAx` and additional assumed project axioms.

The versions are pinned:

| Component | Version |
|---|---|
| Lean | `v4.35.0-rc2` |
| mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Transitive dependencies | [`lake-manifest.json`](lake-manifest.json) |

The lockfile fixes the dependency versions used to check the proof. See
[verification details](docs/VERIFICATION.md) for the commands and trust
assumptions. The formalization has not undergone independent peer review.

## Read the proof

The argument extends a hypothetical short algorithm to an algebraic closure
and chooses a representative minimizing the sum of ranks in its first
coefficient family. Positive conductor growth yields a single pair
replacement that decreases this sum. Zero growth produces physical atoms;
a residual reconstruction argument excludes four atoms, and a
second-conductor budget excludes the remaining three-atom case.

[The proof overview](docs/PROOF_OVERVIEW.md) links these steps to their Lean
modules. The Lean source comments are mostly in Russian; this README,
the public theorem interface and the accompanying guides are in English.

The source entry points are:

| File | Purpose |
|---|---|
| [PublicTheorem.lean](MMRank/PublicTheorem.lean) | The statement for arbitrary linear input forms |
| [Algorithm.lean](MMRank/Algorithm.lean) | Exact algorithms, row action and the trace identity |
| [LengthTwentyOneFirstRank.lean](MMRank/LengthTwentyOneFirstRank.lean) | The main contradiction argument |
| [scripts/Audit.lean](scripts/Audit.lean) | The theorem signatures and axiom audit |

## Related work and scope

Laderman's [23-multiplication algorithm (1976)](https://doi.org/10.1090/S0002-9904-1976-13988-2)
works over every field. Bläser's
[*On the complexity of the multiplication of matrices of small formats*
(2003)](https://doi.org/10.1016/S0885-064X%2802%2900007-9)
established the classical lower bound of 19.

Recent work has determined the rank over the two-element field $\mathbb F_2$.
The following sequence concerns that specific field:

| Work | Result over $\mathbb F_2$ | Method |
|---|---|---|
| Chengu Wang, [*Automated Lower Bounds for Bilinear Complexity over Finite Fields*](https://arxiv.org/abs/2603.07280), 2026 | $R\geqslant20$ | Automated bounds and checkable certificates |
| Chengu Wang, [*A Lower Bound of 21 for 3 × 3 Matrix Multiplication over F₂*](https://arxiv.org/abs/2609.06725), 2026 | $R\geqslant21$ | Subspace bounds and exhaustive profile search |
| Shuxing Yang et al., [*A Structural Proof of the Lower Bound 21 for 3 × 3 Matrix Multiplication over F₂*](https://arxiv.org/abs/2609.18722), 2026 | $R\geqslant21$ | Structural argument with certified finite bounds; Lean formalization |
| Isaac Rudich and Louis-Martin Rousseau, [*Lower Bound of 22 for 3x3 Matrix Multiplication over the Integers*](https://arxiv.org/abs/2610.01639), 2026 | $R\geqslant22$ | Certified quotient bounds; Lean formalization |
| Tejasvi Singh Tomar, [*The rank of 3 × 3 matrix multiplication over F₂ is 23*](https://arxiv.org/abs/2610.11823v1), 2026 | $R=23$ | Exhaustive search with Lean certificate checkers; compiled evaluation for the largest checks |

The results of Rudich–Rousseau and Tomar also give lower bounds for
algorithms with integer coefficients. Tomar's paper, Section 8, describes
the additional reliance on compiled evaluation (`native_decide`) in its
formal verification.

The theorem in this repository applies uniformly to **every field**. The
stronger numerical bounds over $\mathbb F_2$ do not by themselves establish
those bounds over arbitrary fields. This repository proves a lower bound
of 21; it does not determine the exact rank over every field. The papers
above provide context and are not assumptions or computational inputs to
the Lean proof.

## Authorship, AI assistance and citation

Andrey Ivanov is the author and responsible maintainer. The research and
formalization were developed with substantial assistance from OpenAI's
ChatGPT/Codex, including mathematical exploration, Lean implementation,
proof refactoring and documentation.

Citation metadata is in [`CITATION.cff`](CITATION.cff).

**License:** [Apache License 2.0](LICENSE). Copyright 2026 Andrey Ivanov.
See [NOTICE](NOTICE). Dependencies retain their own licenses.

[^pronunciation]: Russian: Андре́й Ивано́в. IPA: [ɐnˈdrʲej ɪvɐˈnof]. Both the given name and the surname are stressed on the final syllable.
