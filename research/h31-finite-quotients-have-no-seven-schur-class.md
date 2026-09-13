---
rg: 2
id: h31-finite-quotients-have-no-seven-schur-class
kind: claim
title: Every finite quotient of H31 has vanishing second cohomology over F7
artifacts:
  - research/artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md
distinct_from:
  h31-seven-central-image-criterion: that proves a conditional equivalence and the known geometry of H31; this asserts the unresolved uniform cohomology vanishing needed to produce the input group.
---

For the explicit group `H_31` of
[[h31-seven-central-image-criterion]], every finite quotient `F`
satisfies

```text
H^2(F;F_7)=0,
```

where the coefficient action is trivial.

The quantifier includes arbitrary finite quotients, not only simple
ones. The condition would supply the concrete prime-`7` input for
[[hyperbolic-finite-images-exclude-a-central-prime]]. It is not
established by the present work.

## Attempts

The vertex-group orders `14880`, `25`, and `625` are prime to `7`.
Local averaging and unique splitting prove
`H^1(H_31;F_7)=H^2(H_31;F_7)=0`. They also prove that every
central `C_7` extension of any finite quotient lifts to `H_31`.
Thus local splitting does not exclude nontrivial finite-quotient
cocycles: any nonsplit such extension would itself be a quotient.

The retraction `c=1` onto `Q=PSL_2(31)` has a kernel `K` whose
quotient triangle complex is a cone with `5`-group stabilizers.
Consequently `H^j(K;F_7)=0` for every `j>0`. Every positive-degree
cohomology group of `H_31` with coefficients in an `F_7[Q]` module
inflated along this retraction vanishes too. This excludes a first
nontrivial elementary abelian `7` extension of `Q` as a quotient
over that map. A deeper quotient in which `c` survives need not have
the same cone quotient or the same cohomology vanishing.

For a specified finite quotient, the artifact gives exact linear
cocycle and presentation-lifting equations. The three power relators
have coefficient matrix `5 I_3`, invertible over `F_7`; this uniquely
fixes the generator corrections, and the remaining lift equations
hold by local splitting. A proof must still show that the cocycle is
a coboundary uniformly over all finite quotients.

The usual property-(T) link criterion cannot supply this conclusion
by itself. Other hyperbolic generalized triangle Kazhdan groups with
vertex-group orders coprime to `3` have finite quotients with
central `3`-torsion. More specific information about all finite
quotients, including possible solvable radicals, remains necessary.
