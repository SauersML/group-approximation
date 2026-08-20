---
rg: 2
id: symmetrized-reset-collapses-schur-flow-to-one-ray-proof
kind: route
title: Solve the child restriction equations after complete type balance
target: symmetrized-reset-collapses-schur-flow-to-one-ray
requires:
  - translation-symmetrized-schur-child-reset
  - translation-symmetrized-full-schur-reset
  - oriented-schur-child-branching-identity
  - shared-overlap-controls-packet-multiplicity-vector
---

The reset theorem says that the multiplicity of every corrected child type
`sigma_(x,+/-)` is the same integer `m`. For `f(x)=1`, `(OCB1)` says the
unique full-packet simple `T_x` restricts as

```text
T_x downarrow_C_f = sigma_(x,+) direct_sum sigma_(x,-).
```

No other full-packet simple lies over `x`, so both child equations force and
are forced by multiplicity `m` of `T_x`.

For `f(x)=0`, there are two full-packet simples `T_(x,+/-)`, and each restricts
to the child simple with the same sign. The two child equations therefore
force multiplicity `m` of each. This proves `(SRC6)`, its converse, and the
one-dimensionality of the compatible cone.

There are `2K_1` child copies above the active sectors and `2K_0` above the
inactive sectors, giving `2(K_1+K_0)m=2^(k+1)m`. The number of full-packet
simples counted with multiplicity is `K_1m+2K_0m`, and the difference is
`K_1m`. Hilbert dimension is

```text
K_1 m(2D)+2K_0 mD=2D(K_1+K_0)m=2^(k+1)Dm,
```

which proves `(SRC7)` and exhibits the scalar stationary compensation.

For the approximate statement, exactify the two fixed finite tables. Their
restrictions approximate the same original `C_f` words, so polar alignment
discards only controlled normalized dimension. Equation `(OMV1)` bounds the
full weighted child-type discrepancy on the common overlap. The exact reset
vector lies on the constant child ray, and the preceding sectorwise inverse
of the restriction equations has coefficients zero or one. Pulling the
discrepancy back through those fixed equations changes the constant only by a
packet-dependent factor, giving `C sqrt(E)`.
