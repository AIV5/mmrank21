# Human-readable proof notes

| Language | PDF | LaTeX source |
|---|---|---|
| English | [Read or download](../../output/pdf/rank21-english-proof.pdf) | [rank21-en.tex](rank21-en.tex) |
| Русский | [Читать или скачать](../../output/pdf/rank21-russian-proof.pdf) | [rank21-ru.tex](rank21-ru.tex) |

These are AI-generated, human-readable expositions of the Lean proof in
this repository, prepared using OpenAI ChatGPT/Codex under the direction
of Andrey Ivanov. They are **proof notes, not research articles**, and have
not undergone independent mathematical or peer review. No claim of novelty
or priority is made for the results or proofs.

The Lean source is the authoritative formal statement and proof. Successful
Lean checking does not certify the correctness of the prose account or its
correspondence to the code. The notes reorganize some lemmas and use matrix
notation; they are not a line-by-line export of Lean. Errors and unclear
passages can be reported through [GitHub issues](https://github.com/AIV5/mmrank21/issues).

The English and Russian texts have matching statement numbers. Both retain
right action on row vectors and the coefficient cycle UVW. They cover the
first-rank-sum descent proof of the lower bound 21 and the consequence
R_K⟨2,2,n⟩ ≥ ⌈7n/2⌉. The latter is formalized in
[TwoByTwoLengthBound.lean](../../MMRank/TwoByTwoLengthBound.lean).
[SOURCE_MAP.tsv](SOURCE_MAP.tsv) maps each labeled statement to its Lean
modules; resolve these paths from the repository root, at the same Git
commit as the notes. This map is a reading aid, not a formal verification
of the prose.

The notes, their LaTeX sources and the Lean code are covered by the
repository's [Apache-2.0 license](../../LICENSE). The existing
[Zenodo DOI](https://doi.org/10.5281/zenodo.23324839) archives version 0.1.1,
which predates these additions. Cite the Git commit when referring to them.
For related work, including Shitov's result for ⟨2,2,n⟩, see the
[repository README](../../README.md#related-work-and-scope).

## Build the PDFs

From the repository root:

```sh
mkdir -p tmp/pdfs/en tmp/pdfs/ru output/pdf
latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=tmp/pdfs/en docs/proof-notes/rank21-en.tex
latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=tmp/pdfs/ru docs/proof-notes/rank21-ru.tex
cp tmp/pdfs/en/rank21-en.pdf output/pdf/rank21-english-proof.pdf
cp tmp/pdfs/ru/rank21-ru.pdf output/pdf/rank21-russian-proof.pdf
```

Requirements: XeLaTeX, latexmk, English and Russian babel support, fontspec,
amsmath/amssymb/amsthm/mathtools, tikz-cd, microtype, enumitem, needspace,
booktabs, longtable, hyperref, fancyhdr, and DejaVu Serif, Sans and Sans Mono
fonts. Each source is self-contained; no external figures are required.
Building the PDFs is optional and separate from `./scripts/check.sh`.
