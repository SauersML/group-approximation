---
rg: 2
id: qutrit-scalar-exactification-has-no-central-index
kind: claim
title: Exact qutrit scalar types give fixed ranks but no conjugacy or central index
artifacts:
  - research/qutrit-scalar-exactification-proof.md
distinct_from:
  one-balanced-actor-qutrit-bridge-is-jacobson-core: that identifies the first non-residually-finite support group; this tests the two immediate Hilbert--Schmidt obstruction mechanisms after exactifying its finite scalar subgroup.
  qutrit-rank-six-parity-bridge-is-impossible-or-virtually-free: that studies a finite Clifford parity cut in the nine-dimensional spin block; this treats arbitrary trace-preserving microstates of the full scalar envelope K=GL_28(F_2).
  weighted-unitary-hall-deficit-gap: that turns an authenticated weighted carrier deficit into a terminal gap; this proves that neither bare actor conjugacy nor a central head supplies such a deficit.
---

Let

```text
K=GL_28(F_2)
```

be the finite scalar envelope containing the qutrit packet. In any
trace-preserving hyperlinear microstate sequence for a group containing
`K`, finite-group Hilbert--Schmidt stability gives, after an
`o(d_l)`-dimensional stabilization, exact representations `sigma_l`
whose normalized characters converge to the regular character of `K`.
Consequently

```text
rank(sigma_l(q))/d_l       -> 1/3,
rank(sigma_l(R))/d_l       -> 2/9,
rank(sigma_l(q-R))/d_l     -> 1/9.                       (QSE1)
```

For any actor unitary `U_l`, conjugation preserves all three ranks.
Therefore a relation which only transports the qutrit cell by conjugacy
cannot create an index or weighted Hall deficit after `K`-exactification.

The finite-central alternative also gives no obstruction. The group
`K=PSL_28(F_2)` is perfect and has trivial Schur multiplier, hence is
superperfect. Every central extension of `K` by an abelian group splits
uniquely. In particular, adjoining a central head involution produces a
direct factor `K x C_2`, not a central phase forced to the identity.

Thus the first possible Hilbert--Schmidt obstruction in the balanced
Jacobson bridge must be noncentral and head-conditioned: it must
authenticate how a raw `S/T` occurrence changes an intersection or polar
carrier inside `R` versus `q-R`. The fixed ranks in `(QSE1)` are then
available to pay a quantitative deficit, but they do not create one without
that extra incidence.
