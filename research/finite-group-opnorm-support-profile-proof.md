---
rg: 2
id: finite-group-opnorm-support-profile-proof
kind: route
title: Average into the regular representation and compare central character projections
target: finite-group-opnorm-support-profile
requires: []
---

First replace the fixed presentation model by an all-pairs map
`phi:H->U(d)`: choose one representative word for each element of `H` and
use the finitely many fixed van Kampen derivations to bound every
multiplication-table error by a presentation-dependent multiple of the
relator defect.

For such an `epsilon`-representation define the isometry

```text
V xi = |H|^(-1/2) sum_(g in H) delta_g tensor phi(g)xi
```

from `C^d` to `ell^2(H) tensor C^d`.  For the right regular representation
`R_h delta_g=delta_(g h^-1)`, the relation

```text
(R_h tensor I)V ~= V phi(h)
```

shows that the range projection `P=VV*` almost commutes in operator norm with
`R(H)`.  Average `P` over that finite action.  For sufficiently small `epsilon`, spectral cut at
`1/2` gives an invariant projection `Q` with `||P-Q||<1` and
`rank(Q)=rank(P)=d`.  The standard close-projections unitary carries
`ran(P)` to `ran(Q)`.  Pulling the right regular action on `ran(Q)` back along
this unitary and `V` produces an exact `d`-dimensional representation `rho`
which is `O_H(epsilon)`-close to `phi`.  All constants depend only on the
fixed finite group and chosen presentation, never on `d`.

For each irreducible `lambda`, its central isotypic projection in an exact
representation is

```text
p_lambda(rho)
 = (dim lambda/|H|) sum_(h in H) conjugate(chi_lambda(h)) rho(h).
```

Hence close exact representations have close `p_lambda`.  If two projections
are at operator-norm distance less than one, they have the same rank.  Choose
the correction radius below the minimum of these finitely many character
projection thresholds.  Any two exact corrections then have the same
isotypic ranks, in particular the same zero-versus-positive support subset.
