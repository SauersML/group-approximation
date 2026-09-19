---
rg: 2
id: mersenne-diagonal-countersequence-is-tracially-regular
kind: claim
title: The diagonal Mersenne countersequence is tracially regular
distinct_from:
  mersenne-phases-refute-diagonal-iwahori-decoder: that proves constant distance from exact diagonal gauges; this shows that every fixed word trace nevertheless has the canonical regular limit.
  regular-iwahori-relative-congruence-exactification: that asks for an actual flexible congruence lift of every regular microstate; this verifies only the trace hypothesis and explicitly does not produce that lift.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that forces regular trace by tensor amplification; this countersequence has regular trace intrinsically, without an auxiliary tensor factor.
---

**ESTABLISHED TRACE FIREWALL.** Let

```text
U_n=(X_n,R_n,T_n)
```

be the Mersenne countersequence from
`mersenne-phases-refute-diagonal-iwahori-decoder`, acting on
`l2(Q_n)`. For every fixed word `w=w(x,r,t)`,

```text
lim_n tr_(Q_n)(w(U_n))
 = 1,  if w=1 in PSL_2(Z[1/2]),
 = 0,  otherwise.                                       (MTR1)
```

Thus the homomorphism defined by `[U_n]` in the tracial matrix
ultraproduct has the regular character of `PSL_2(Z[1/2])`.

The conclusion is unchanged by either of the operations allowed in
flexible generalized Hilbert--Schmidt comparison:

1. adjoining `o(|Q_n|)` arbitrary dimensions; or
2. replacing the marked generators by tuples at normalized-HS distance
   tending to zero through almost-full isometries.

Consequently no obstruction depending on finitely many normalized traces
of fixed words, nor any continuous function of such traces, can show that
the Mersenne tuples are far from flexible exact endpoints. In particular,
the diagonal Hamming gap is invisible to the regular-character test.

This is a sharp no-go for a trace-invariant promotion of the diagonal
countersequence. It neither constructs a nondiagonal or padded exact
endpoint nor proves that one exists. The relative finite-dimensional
lifting problem, and hence the non-hyperlinearity root, remain open.

DERIVATION
mersenne-monomial-words-have-regular-trace-proof
