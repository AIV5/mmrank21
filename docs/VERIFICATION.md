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

`scripts/check.sh` performs the following checks:

1. `lake build` builds the library rooted at `MMRank.lean`, including the
   public theorem and all its imports, and the proved `Solution` interface.
2. `lake env lean scripts/Audit.lean` prints the public theorem and the
   exact-algorithm theorem, prints their axiom dependencies, and audits
   every declaration in the imported MMRank modules, including generated
   helpers. It also checks the axioms of `MMRank.Palomar.lower_bound` in Solution.
   Explicit `import all` directives retain access to private helpers under
   Lean's module system. The shell script checks that every proof source has
   such an import in the audit, so adding a module cannot silently reduce coverage.

The audit rejects any axiom outside `propext`, `Classical.choice` and
`Quot.sound`, the standard foundations used here by Lean/mathlib. In
particular, it rejects `sorryAx`, additional assumed mathematical axioms,
and the extra evaluation axioms associated with `native_decide`.
An audit of an empty project also fails.

On success the final line reports:

```text
PASS: 1842 project declarations use only propext, Classical.choice, Quot.sound.
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

## Comparator

The pinned Lean toolchain includes Comparator, `leanexport`, and NanoDa.
Install Bubblewrap (`bwrap`) using your operating system's package manager;
the operating system must permit its user-namespace sandbox. The outer `lake env`
adds the pinned toolchain binaries, including `nanoda_bin`, to PATH. From the project
root, run:

```sh
lake env lake comparator --config comparator.json
```

`Challenge.lean` imports only Mathlib and declares the exact unrestricted
matrix-multiplication statement. It intentionally contains one `sorry`.
`Solution.lean` separately proves that statement by applying
`MMRank.matrix_multiplication_length_ge_twenty_one`; it never imports Challenge.
Both sides call the compared declaration `MMRank.Palomar.lower_bound`.
There are no project-specific definitions in the Challenge to reinterpret.

Comparator builds and exports the two environments separately, compares the
statements and their dependencies, checks the permitted axioms, and replays
the exported proof. `enable_nanoda: true` requests the independent NanoDa
checker in addition to Lean's own kernel. Keep this setting enabled when
reproducing the Palomar configuration. The ordinary audit still rejects
`sorryAx` in the proof development; the isolated Challenge placeholder is not
part of that development or its default build targets.

An exit code of zero confirms this local mechanical check. It does not claim
Palomar registration, an editorial decision, mathematical novelty, or human
peer review. The source migration to Lean's `module` system preserves the
existing mathematical statements and proof bodies; public imports and exposed
public sections retain the interfaces used between modules.
