---
rg: 2
id: bounded-relator-area-controls-opnorm-word-defect
kind: claim
title: Bounded relator area gives dimension-free operator-norm word control
distinct_from:
  conjugacy-addressed-opnorm-challenges-are-lossless: that is the zero-cost special case of transporting one discrepancy by conjugation; this controls an arbitrary product of a bounded number of conjugated defining relators.
  bounded-area-high-chromatic-conjugacy-collapse: that uses normalized Hilbert--Schmidt Carmichael relations; this is the norm-independent presentation estimate used by the operator-norm commutator code.
---

Let

```text
Gamma=<S | R>,                    R finite,
Def_R(U)=max_(r in R)||r(U)-I||_op.
```

If a free word `w` has relator area at most `A`, meaning

```text
w=product_(k=1)^A g_k r_k^(epsilon_k) g_k^(-1),
r_k in R,                         epsilon_k in {+1,-1},
```

then every unitary tuple `U` satisfies

```text
||w(U)-I||_op <= A Def_R(U).                              (BRA1)
```

The bound is independent of the matrix dimension and of the lengths of the
conjugating words `g_k`.  Only the number of relator cells is charged.

