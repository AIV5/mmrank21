# Verifying the formal proof

The proof is checked by Lean 4 with mathlib. Install
[elan](https://github.com/leanprover/elan#installation), ensure that `lake`
is on your PATH, and run these commands from the repository root:

```sh
lake exe cache get
./scripts/check.sh
```

Git and Bash are needed. The first command downloads compiled dependencies;
it requires network access. `lean-toolchain` selects Lean `v4.35.0-rc2`,
and `lake-manifest.json` fixes all dependency revisions. Keep these files
unchanged when reproducing the supplied proof.

## What the script checks

`scripts/check.sh` runs two commands:

1. `lake build` builds the library rooted at `MMRank.lean`, including the
   public theorem and all its imports.
2. `lake env lean scripts/Audit.lean` prints the public theorem and the
   exact-algorithm theorem, prints their axiom dependencies, and audits
   every declaration in the imported MMRank modules, including generated
   helpers.

The audit rejects any axiom outside `propext`, `Classical.choice` and
`Quot.sound`, the standard foundations used here by Lean/mathlib. In
particular, it rejects `sorryAx`, additional assumed mathematical axioms,
and the extra evaluation axioms associated with `native_decide`.
An audit of an empty project also fails.

On success the final line reports:

```text
PASS: 1925 project declarations use only propext, Classical.choice, Quot.sound.
```

A nonzero exit status from either command makes `scripts/check.sh` fail.
The [GitHub Actions workflow](../.github/workflows/lean.yml) runs the build
and the same audit automatically on pushes and pull requests.

## Inspecting the claim

[PublicTheorem.lean](../MMRank/PublicTheorem.lean) states the lower bound
for arbitrary linear input forms and output matrices over any field.
[The statement guide](STATEMENT.md) explains its translation to trace
coefficients and right action on row vectors. Inspection of that signature
is essential: successful checking certifies the formal statement actually
written in the source.

The proof requires no external search certificates or numerical datasets.
Checking relies on the pinned Lean implementation and its imported
libraries. The axiom audit is performed within Lean; it is not an
independent implementation of the kernel or a substitute for mathematical
peer review.
