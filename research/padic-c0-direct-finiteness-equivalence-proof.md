---
rg: 2
id: padic-c0-direct-finiteness-equivalence-proof
kind: route
title: Lift through one plus p and kill a small p-adic idempotent
target: padic-c0-direct-finiteness-equivalence
requires: []
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

## Direct proof

It is enough to write the scalar proof, because the same argument applies to
the matrix Banach algebra with its maximum entry norm.

Suppose `C_p(G)` is directly finite and `ab=1` in `F_p[G]`.  Choose
finite-support lifts `A,B in Z_p[G]`.  Then `AB=1+pC`, and `||pC||_p<1`, so
`AB` is invertible by its Neumann series.  Put `B'=B(AB)^(-1)`.  Now `AB'=1`;
direct finiteness gives `B'A=1`.  Modulo `p`, `(AB)^(-1)` becomes `1`, so this
last equality reduces to `ba=1`.

Conversely suppose `F_p[G]` is directly finite and `AB=1` in `C_p(G)`.
Reduction modulo `p` has finite support for every `c_0` element, hence
`bar(A)bar(B)=1` and direct finiteness gives `bar(B)bar(A)=1`.  Thus
`D=1-BA` lies in `pC_p(G)`.  Since `AB=1`, both `BA` and `D` are idempotent.
If `D != 0`, then

```text
0 < ||D||_p < 1,       ||D||_p=||D^2||_p <= ||D||_p^2,
```

which is impossible.  Therefore `BA=1`.
