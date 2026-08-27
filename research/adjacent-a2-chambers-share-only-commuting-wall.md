---
rg: 2
id: adjacent-a2-chambers-share-only-commuting-wall
kind: claim
title: Adjacent A2 chambers share only a commuting wall, and exact regular packets can rotate across it
distinct_from:
  one-shared-root-does-not-align-heisenberg-packets: that identifies one central root with one simple root; this matches the complete two-root wall shared by actual adjacent A2 chambers and gives the explicit off-wall cross-Gram scalar.
  heisenberg-chamber-clocks-escape-until-root-gluing: that duplicates every shared occurrence in separate chamber factors; this uses one literal pair of commuting matrices for both adjacent exact regular packet representations.
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that aligns local constraint types but leaves context operators unrelated; this is the A2 root-specific regular-Heisenberg version and computes the precise conditional-expectation obstruction.
---

In the standard positive chamber of the `A_2` root system, write

```text
H_1=<x_12,x_23,x_13 : [x_12,x_23]=x_13, x_13 central>.  (ACW1)
```

After the simple reflection `s_12`, the adjacent positive chamber is

```text
H_2=<x_21,x_13,x_23 : [x_21,x_13]=x_23, x_23 central>.  (ACW2)
```

Their common positive roots are exactly

```text
{13,23}.                                                 (ACW3)
```

They commute.  Hence there is no second **noncommuting** geometric root
shared by two distinct adjacent chambers.  The central/simple roles are
exchanged across the wall: `x_13` is central in `(ACW1)` and simple in
`(ACW2)`, while `x_23` is simple in `(ACW1)` and central in `(ACW2)`.

This elementary root geometry already prevents a two-generator uniqueness
argument on one chamber overlap.

## Exact regular wall-rotation countermodel

Let `H_p=<x,y,z>` be the finite Heisenberg group over an odd prime field,
with `[x,y]=z`, and let `lambda` be its left regular representation on
`E=l^2(H_p)`.  Put

```text
K=<y,z> isomorphic to C_p^2.                              (ACW4)
```

The restricted representation `lambda|K` is `p` copies of the regular
representation of `K`.  The automorphism of `K` swapping `y` and `z`
therefore has a unitary implementer `S in U(E)`:

```text
S lambda(y) S^*=lambda(z),
S lambda(z) S^*=lambda(y).                               (ACW5)
```

Define

```text
rho_1=lambda,                 rho_2=Ad(S) compose lambda. (ACW6)
```

Interpret the actual wall words by

```text
x_23 = rho_1(y)=rho_2(z),
x_13 = rho_1(z)=rho_2(y).                                (ACW7)
```

Thus both shared raw group words are literally the same matrices in the two
packets.  Both packet representations have the exact regular character, and
their complete common wall algebra

```text
D=C^*(lambda(y),lambda(z))                               (ACW8)
```

is identical.  Every scalar moment and every spectral projection belonging
to the two shared roots agrees exactly.

Nevertheless

```text
A_1=C^*(rho_1(H_p)) != A_2=C^*(rho_2(H_p)).              (ACW9)
```

Indeed `lambda(z)=rho_2(y)` is central in `A_1` but noncentral in `A_2`;
equivalently `lambda(y)=rho_2(z)` is noncentral in `A_1` but central in
`A_2`.  Equality of the algebras would contradict either role exchange.

As in `one-shared-root-does-not-align-heisenberg-packets`, tensoring with
two independent bits supplies projections `P,Q` and a transport
`V=S tensor Swap` such that

```text
VPV^*=Q,
[P,Q]=0,
tr(P)=tr(Q)=1/2,
tr(PQ)=1/4,                                               (ACW10)
```

while both wall roots remain literal and both packets remain exact regular.
Thus adding the second actual shared root does not repair the multiplicity
rotation.

## Explicit off-wall cross-Gram scalar

Let

```text
X_2=rho_2(x)
```

be the root of the second chamber which is not on the common wall, and let
`E_1` be trace-preserving conditional expectation onto `A_1`.  Since the
regular group matrices `{rho_1(g):g in H_p}` are an orthonormal basis of
`A_1` for normalized Hilbert--Schmidt inner product,

```text
||E_1(X_2)||_2^2
  = sum_(g in H_p) |tr(rho_1(g)^* X_2)|^2.               (ACW11)
```

Consequently the exact mixed-reservoir defect is

```text
Delta_mix
 = dist_2(X_2,A_1)^2
 = 1-sum_(g in H_p) |tr(rho_1(g)^* X_2)|^2.              (ACW12)
```

In the countermodel `Delta_mix>0`: if `X_2` belonged to `A_1`, then the two
shared wall generators together with `X_2` would put `A_2` inside `A_1`;
the two faithful regular packet algebras have the same dimension `|H_p|`, so
they would be equal, contradicting `(ACW9)`.

All cross-Gram moments whose two entries lie in the wall algebra `D` are
already exact in this model.  Therefore no wall-only moment, even the full
joint PVM/Gram table of both literal shared roots, can bound `(ACW12)`.

## Consequence for the arithmetic atlas

Pairwise adjacent-chamber gluing cannot supply the desired common reservoir:
the actual overlap is abelian and admits the exact role-rotation above.  A
positive estimate must use a closed chamber gallery so that an off-wall root
eventually returns as a constrained root.

It would be incorrect to force `Delta_mix` itself to zero.  Even in an honest
regular representation of the common Chevalley group `SL_3(F_p)`, an
off-wall root is not in the first unipotent packet algebra, so `(ACW12)` is
positive (indeed the corresponding group basis elements are orthogonal).
The local packet algebras are supposed to remain distinct subalgebras of one
ambient coefficient reservoir.  The correct scalar is instead the defect of
the closed-gallery transition holonomy:

```text
||Omega_transition-I||_2^2
 <= C (relator defect + canonical trace defect).         (ACW13)
```

For the fixed period-five packet,
`six-chamber-a2-holonomy-closes-fixed-clock-sector` proves this on the minimal
six-edge Coxeter gallery, whose raw holonomy is `(n_12 n_23)^3=1`.  Vanishing
holonomy puts the distinct local packets in one coherent Chevalley reservoir;
the rank-two diagonal triangle then kills the remaining gauge.

The countermodel proves that replacing the closed circuit by any amount of
pairwise wall data is insufficient.

This also locates the missing input in the congruence-conductor formulation.
Each coweight direction has its own kernel-join descent, and its Weyl orbit
can generate the full shallower principal layer only after those directional
descents act on one carrier.  Pairwise wall equality supplies merely the
common abelian algebra `D` and does not identify their off-wall multiplicity
spaces.  A circuit estimate proving `(ACW13)` would place the distinct packet
algebras coherently in one ambient reservoir; the directionwise kernel joins
could then be summed there and the fixed `Lambda_0` property-T gap applied.
Thus closed-gallery holonomy, rather than pairwise `Delta_mix` or another
conductor index calculation, is the scalar interface to a uniform recurrence.
