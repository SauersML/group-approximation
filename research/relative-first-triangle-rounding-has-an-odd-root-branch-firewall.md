---
rg: 2
id: relative-first-triangle-rounding-has-an-odd-root-branch-firewall
kind: claim
title: Independent first-triangle rounding loses the odd square-root branch at constant HS cost
distinct_from:
  bs14-cubic-rounding-leaves-relative-core-basin: that rounds both cubic words under exact dihedral hypotheses and isolates an operator-norm relative product; this gives an explicit normalized-HS obstruction already for the first modular triangle and its square-root return to the BS root.
  bs14-hs-stability-does-not-supply-relative-op-basin: that separates normalized-HS from operator-norm basin entry and leaves a hypothetical relative correction open; this exhibits the concrete positive-density branch fold that any relative correction must prevent.
  flexible-bs-cycle-surgery-absorbs-exact-coboundaries: that repairs gauges inside the exact root commutant after an exact coboundary exists; the present mismatch rotates nearly antipodal root eigenspaces and is uniformly far from every root of the rounded square.
---

There are exact finite congruence Iwahori tuples `(X_0,R,S)` of dimensions
`d_p->infinity`, unitaries `X_p`, and exact order-three unitaries `A_p` such
that

```text
X_p^2=1,             A_p^3=1,
||X_p S^2-A_p||_2 <= 2 pi/p,                          (FTR1)
Q_p:=X_p A_p,        ||Q_p-S^2||_2 <= 2 pi/p,          (FTR2)
```

but every unitary square root `T^2=Q_p` satisfies

```text
||T-S||_2 >= sqrt((p-1)/p) cos(pi/(2p)).               (FTR3)
```

Consequently the near first-triangle tuple `(X_p,S)` has

```text
||(X_pS^2)^3-1||_2 <= 6 pi/p,                         (FTR4)
```

and admits an independently rounded exact `PSL_2(Z)=C_2*C_3` vertex
`(X_p,A_p)` at vanishing cost, but its product has no square root near the
original BS root.  Thus the proposed alternating step

```text
round (X,XS^2) as a modular vertex
 -> set S_new^2=X_new A_new
 -> re-exactify the BS core
```

has no dimension-free small-displacement guarantee.  The obstruction is
not two-primary: it occurs inside every sufficiently large odd prime
congruence packet because the square map nearly identifies antipodal odd
roots.

This does not refute full relative Iwahori stability.  It proves that the
first triangle cannot be rounded independently.  A convergent scheme must
round the vertex together with a chosen lift of its product through the
square map, and must use the inversion/second-cubic rows to forbid the wrong
branch before changing the vertex.

