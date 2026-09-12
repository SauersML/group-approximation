---
rg: 2
id: depthwise-opnorm-collapse-implies-mf-radical
kind: claim
title: Depthwise operator-norm collapse with arbitrary loss implies MF-radical membership
distinct_from:
  depthwise-canonical-kleene-needs-no-uniform-runtime-gap: that is a machine-indexed normalized-HS criterion with finite canonical trace windows; this is the trace-free operator-norm lemma for one recursively presented group.
  fixed-depth-canonical-mark-estimates-rule-out-hyperlinearity: that treats canonical-profile Hilbert--Schmidt microstates and a tracial mark; this treats every norm-corona homomorphism and a group word.
  uniform-finite-mf-obstruction: that produces one finite test and one positive uniform threshold for the literal group; this allows a sequence of finite tests with completely unrestricted finite constants.
---

Let `Gamma=<S|R_infty>` be finitely generated and recursively presented, and
let `w` be a word.  Suppose there are finite sets

```text
R_N subset R_infty,
```

numbers `b_N->0`, and finite constants `C_N` such that every
finite-dimensional unitary tuple `U` satisfies

```text
||w(U)-I||_op <= b_N + C_N Def_(R_N)(U)                 (DOC1)
```

for every `N`.  Then

```text
w in Res_MF(Gamma).
```

There is no restriction on the growth or computability of `C_N`.  The order
of limits is load-bearing: fix `N`, let the matrix-corona coordinate tend to
infinity so that the finite relator defect vanishes, and only then let
`N->infinity`.
