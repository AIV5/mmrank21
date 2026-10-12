# From matrix multiplication to the Lean statement

The public theorem in [PublicTheorem.lean](../MMRank/PublicTheorem.lean)
uses only a field, a finite index set, ordinary 3 × 3 matrices, linear forms,
and the identity

```text
A * B = sum_i (a_i(A) * b_i(B)) • W_i, for all A and B.
```

`Fin 3` is the three-element coordinate type. `Fintype.card I` counts the
terms, `→ₗ[K]` denotes a K-linear map, and `•` is scalar multiplication of
the output matrix. The hypothesis is exact equality for all inputs.
There is no assumption on the value of the minimum rank in this signature.

The theorem underlying this interface is expressed using
[`ExactAlgorithm`](../MMRank/Algorithm.lean). Its only mathematical data are
three families of matrices and their exactness identity. For finite
coordinate types P, Q, S, the shapes are:

| Matrix | Shape |
|---|---|
| U_i | P × Q |
| V_i | Q × S |
| W_i | S × P |
| A | Q × P |
| B | S × Q |
| C | P × S |

The defining equation is

```text
B * A = sum_i (trace(U_i * A) * trace(V_i * B)) • W_i.
```

The coefficients act on row vectors on the right:

```text
U_i : (P → K) → (Q → K)
V_i : (Q → K) → (S → K)
W_i : (S → K) → (P → K).
```

Thus the coefficient cycle is **UVW**, with P → Q → S → P. The input cycle
is **CBA**, with P → S → Q → P. The equivalent trilinear identity is

```text
trace(C * B * A) = sum_i trace(U_i * A) * trace(V_i * B) * trace(W_i * C).
```

These conventions are part of the formal development, not just notation in
this guide. `rowLinear_mul` proves
`(U * V).vecMulLinear = V.vecMulLinear.comp U.vecMulLinear`, expressing
first U, then V on a row vector. `Coefficients.isExact_iff_traceIdentity`
proves equivalence of the bilinear and trilinear identities, and
`ExactAlgorithm.rotate` preserves exactness under the cyclic shift
(U, V, W) ↦ (V, W, U). All three are in
[Algorithm.lean](../MMRank/Algorithm.lean).

Matrix multiplication itself has its usual meaning. The shorter public
statement uses AB and arbitrary linear forms; its proof explicitly translates
to the row convention above.

Every linear form f on matrices has a unique trace representation
`f(X) = trace(X * T)`. This is proved in
[`exists_unique_trace_representation`](../MMRank/TraceDuality.lean), without
division by the matrix dimension. Hence it also applies in characteristics
2 and 3. To obtain the public A * B formulation, the wrapper swaps the two
input names, represents b by U and a by V, and uses trace cyclicity and
commutativity of scalar multiplication. The formal proof performs these
steps explicitly.

The exact-algorithm theorem permits arbitrary coordinate types of cardinality 3;
the public interface fixes the coordinates to `Fin 3`. The field is
arbitrary in both signatures. Algebraic closedness and genericity enter
only inside the proof, after extending a hypothetical algorithm to an
algebraic closure.

The interpretation as tensor rank uses the standard identification of a
bilinear map with a tensor in the two input dual spaces and the output
space. The Lean theorem states the conclusion directly for all bilinear
decompositions, rather than defining a separate numerical rank function.
