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
first triangle cannot be rounded independently **and then returned to the
old `S` coordinate by square-root selection**.  The stronger coordinate
change `iwahori-square-free-bs14-presentation` bypasses that operation:
write `T=S^2`, round the product directly as `T`, and recover `S` only after
the coupled endpoint `(R,T)` has been authenticated.  The inversion and
second-cubic rows remain necessary for that joint authentication.

The necessary extra coordinate is now explicit.  By
`fourth-power-covariance-unfolds-square-root-branches`, the Hadamard unitary
in this example satisfies

```text
||URU^*-R||_2
 >=(1/2)sqrt((p-1)/p)cos(pi/(2p))-2pi/p ->1/2.
```

Thus joint alignment of `R` and `S^2` forbids the branch with a
dimension-free linear estimate and automatically returns `S`.  The
firewall rules out independent vertex rounding, but it does not require a
new spectral root selector once the BS implementer has been authenticated.

In fact `iwahori-square-free-bs14-presentation` eliminates this selector
from the presentation entirely: with `T=S^2`, the old root is the word
`S=R^(-1)T^2R`, and the relative cubics are `(XT)^3` and `(XT^2R)^3`.
Thus the firewall is now best read as a no-go for discarding the `R`
coordinate during rounding, not as a residual obstruction in the endpoint.

## Ultraproduct consequence

The same example is a literal failure of the relative square-root lifting
step, not merely a bad quantitative estimate.  Pass to any ultrafilter along
`p->infinity` and put

```text
s=[(S_p)],                 q=[(Q_p)]
```

in the tracial matrix ultraproduct.  Equation `(FTR2)` gives

```text
q=s^2                                                   (FTR5)
```

exactly in the quotient.  Nevertheless `(FTR3)` gives

```text
liminf_p inf { ||T-S_p||_2 : T in U(d_p), T^2=Q_p } >= 1.  (FTR6)
```

Thus the exact quotient root `s` has no coordinatewise exact roots of the
**already rounded** products `Q_p` converging to its chosen representatives.
This does not contradict ordinary HS stability of the equation `t^2=q`:
one may change `Q_p` back to `S_p^2` by `o(1)`.  It refutes precisely the
relative path-lifting assertion needed by the alternating scheme, where the
first vertex has already been exactified and its product `Q_p` is held fixed.

Consequently neither compactness of the tracial ultraproduct nor exactness
of `(FTR5)` supplies that particular coordinate lift.  This is a firewall
for the square-root recovery scheme, not for the current square-free
strategy: `(R,T)` endpoint authentication avoids asking for the lift at all.
