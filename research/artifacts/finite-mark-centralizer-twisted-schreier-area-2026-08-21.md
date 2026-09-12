# A twisted Schreier coefficient kills every ambient centralizer shortcut

**Date:** 2026-08-21

## The theorem

Let `G=<X|R>` be finitely presented and let `b` have finite order.  For a
fixed word `beta` representing `b`, the filling areas

```text
Area_R([beta,eta])
```

are proper as the represented elements `h` range through distinct cosets of
`<b>` in `C_G(b)`.  The estimate is linear in distance in the Schreier graph
`<b>\G`.

This remains true when diagrams use every relator of the ambient
presentation.  Thus a split or transport cell cannot provide a bounded-area
shortcut around the centralizer corridor.

## Coefficient system

Choose a prime `p` dividing the order of `b`, map `<b>` onto `C_p`, and take
the direct sum of all `p-1` Galois-conjugate nontrivial characters.  The
resulting local system over `<b>\G` gives the `b` loop diagonal holonomy
`Z=diag(zeta,...,zeta^(p-1))` at every vertex represented by an element of
`C_G(b)`.  The Galois sum is essential: one complex embedding alone need not
give a uniform integral lower bound for general finite order.

For `h in C_G(b)`, the commutator loop consists of an `eta` path from the
base coset to the coset of `h`, a `b` loop there, and the return path.  The
outgoing and return chains have coefficients differing by `Z`.  Reduction
modulo `(1-zeta)` is the ordinary `F_p` path chain, so its support contains a
path between the endpoint cosets.  Algebraic norm then gives

```text
||chain_chi([beta,eta])||_1
 >= a_p d(<b>,<b>h)-2(p-1)|beta|,
```

where `a_p=2 sin(pi/p)`.

Each defining-relator cell has uniformly bounded twisted boundary norm.
Summing cell boundaries proves the area lower bound.

The obstruction also survives averaging individual certificates.  In a
packet of `M` distinct centralizer cosets, at most `M B_R` ordered pairs lie
within Schreier distance `R`, where `B_R` is the finite radius-`R` ball size.
Thus at least half the pair commutators have area at least `A R-B` once
`M>=2B_R+1`, and the mean pair area tends to infinity.

## Consequence for the Thompson common-pivot route

In `thompson-v-r5-uniform-common-pivot-centralizers`, the corrections

```text
s_(ij)=(c_1 c_j)
```

centralize the fixed order-three word `b_0` and give arbitrarily many
distinct cosets modulo `<b_0>`.  Their commutator filling areas must therefore
be unbounded in the full Bleak--Quick presentation.  This refutes the uniform
centralizer target, including proofs which try to use R2/R3 to leave and
re-enter the support stabilizer.

The result does not refute every Carmichael or averaged synchronization
strategy.  It refutes the specific common-frame reduction whose endpoint
corrections are individual centralizer commutators.  A surviving construction
must cancel holonomy only after combining several edges or use a certificate
which never asks for uniformly bounded individual loops `[b_0,h]`.

There is a sharp limitation to the detector: it is linear.  Chains of several
boundary loops can cancel after the loops are assembled into a cycle (and an
inverse pair cancels completely), even when every loop separately has large
area.  Therefore this theorem does not exclude a genuinely collective
positive matrix inequality.  Such an inequality must orthogonalize edge
errors or otherwise prevent cycle cancellation; one scalar product diagram
cannot by itself control the average of the individual normalized-HS norms.
