---
rg: 2
id: atlas-a4-t30-energy-ceiling-below-q14-wall
kind: claim
title: The A4 packet and collision 19243 force aligned t30 root energy below one half
distinct_from:
  atlas-a4-root-energy-ellipse-ceiling: that asks for a much smaller two-coordinate ellipsoidal bound sufficient against the S3 wall; this asks only for one t30 coordinate below the stronger q14 wall.
  atlas-q14-forces-t30-covariance-floor: that is the established opposite lower bound supplied by a second kernel relation; this is the missing packet-plus-19243 upper estimate.
artifacts:
  - experiments/atlas_q14_t30_wall.py
  - experiments/atlas_triangle_19243_packet.py
  - experiments/atlas_a4_gl5_packet_screen.py
---

Let `U_n` be a normalized exact-regular A4 context-network sequence in the
fixed reference-aligned coordinates.  Assume that all thirty shortest A4
packet defects tend to zero and that

```text
||q_19243(U_n)-1||_2 ->0.                             (T30-19243)
```

With `h_n=rho_n(t30)`, prove

```text
limsup_n x_30(U_n)^2
 =limsup_n [1-Re tau_n(U_n h_n U_n^* h_n)] <1/2.      (T30-CEIL)
```

Equivalently,

```text
limsup_n ||U_n h_n U_n^*-h_n||_2^2 <1.
```

This is now the shortest A4 analytic endpoint.  The independent kernel
relation `q_14` forces the opposite lower bound `liminf x_30^2>=1/2`, so no
full S3 recovery or four-variable root ellipse is needed once `(T30-CEIL)` is
proved.

## Exact augmented-zero audit

`atlas-q14-augmented-zero-set-has-x30-one-escape` proves that packet plus
19243 plus q14 has an exact finite-factor solution with `x_30^2=1`.  It also
proves that any exact finite-dimensional solution would yield a regular
finite-quotient solution with `x_30^2=1`.  Therefore `(T30-CEIL)` cannot be a
nonvacuous pointwise inequality derived from matrix positivity or finite-group
representation types.  It is equivalent in substance to a uniform positive
joint-relator gap excluding the entire augmented matrix-microstate tower.  Any
valid proof must use a matrix/CE-sensitive nonliftability input; universal
tracial SOS and exact-zero optimization point in the opposite direction.

## Attempts and constraints

- **Collision 19243 is essential.**  The exact q14 audit finds `11` inner and
  `10` outer classical alignments satisfying both the thirty-relation packet
  and q14.  Therefore packet plus q14 cannot imply `(T30-CEIL)`.  The upper
  proof must use 19243 or another condition that excludes precisely these
  survivors.
- **The exact classical boundary is empty with 19243.**  Among the `30+30`
  packet-compatible A8 automorphism alignments, none satisfies 19243.  In the
  first rank enlargement, exactly `202` of `9,999,360` `GL5(F2)` positions
  satisfy the packet and again none satisfies 19243.  This supports a
  stability theorem but does not itself control arbitrary multiplicity.
- **Work in the shifted geometry.**  The local constraints are the shifted
  products `C_a R C_b` from
  `atlas-a4-packet-centralizer-product-compiler`, not unshifted products of
  centralizers.
- **Use the four holonomies.**  Tree gauge leaves only one `K_(2,2)` and three
  `K_(2,4)` rectangle holonomies.  A dimension-free inequality need only
  control the `t30` covariance through these four multiplicity unitaries and
  the 19243 residual.
- **Use the exact parabolic--C3 bridge.**
  `atlas-t30-is-one-parabolic-c3-bridge` proves
  `t30=(h6_2 k_0)^-1 z b(h6_2 k_0)` and hence
  `x30^2<=3E_PC3`.  The remaining upper estimate may therefore be attacked as
  the four-coordinate weighted ceiling
  `atlas-a4-parabolic-c3-bridge-energy-ceiling`, with the non-strict threshold
  `1/6`; `unitary-products-obey-the-spherical-chord-bound` supplies the strict
  gap at that boundary.
- **Spherical curvature preserves the margin.**  The Euclidean telescoping
  estimate suggested that a non-strict energy ceiling at `1/6` would be
  insufficient.  `unitary-products-obey-the-spherical-chord-bound` removes
  that artifact: `E_PC3<=1/6+o(1)` already gives the strict bound
  `x30^2<=2 sin^2(6 asin(1/12))+o(1)<1/2`.

## Exact analytic reduction and remaining identity

There is an equally short two-holonomy formulation.  Put

```text
c=hk,                 a=zb,
E_2HOL(U)=2 delta_U(c)^2+delta_U(a)^2,
delta_U(g)=||U rho(g)U^*rho(g)^*-1||_2.
```

The established word identity in `atlas-t30-is-one-parabolic-c3-bridge` is

```text
t30=c^-1 a c.
```

Together with `unitary-products-obey-the-spherical-chord-bound`, this gives

```text
2 f(delta_U(c)^2)+f(delta_U(a)^2)
 <=3 f(E_2HOL(U)/3),
f(s)=asin(sqrt(s)/2),

x30(U)^2 <=2 sin^2(3 f(E_2HOL(U)/3))
```

Consequently the non-strict endpoint requested by
`atlas-a4-two-holonomy-reflection-energy-ceiling`,

```text
limsup E_2HOL(U_n)<=1/3,
```

already implies the strict numerical conclusion

```text
limsup x30(U_n)^2
 <=2 sin^2(3 asin(1/6))
 =338/729 <1/2.
```

Thus neither word telescoping nor the strictness at the endpoint is missing.
The unresolved step is a multiplicity-uniform estimate on the two endpoint
holonomies.  A sufficient (stronger) form would be: for some absolute finite
constant `C`,

```text
E_2HOL(U) <= C (D_packet(U)+||q_19243(U)-1||_2^2).            (ENDPOINT)
```

Here `D_packet` is any fixed sum of the thirty squared packet defects.
`(ENDPOINT)` would force `E_2HOL(U_n)->0`, hence is more than the needed
ceiling.

The existing rectangle identities do not prove `(ENDPOINT)`.  After tree
gauge, `h` lies in the `K_(2,2)` packet component, while `k` and `z` lie in
the `K_(2,4)` component; `b` is supplied only by the collision word.
Therefore `c=hk` and `a=zb` are cross-component endpoint products, rather
than any of the four rectangle holonomies.  The missing identity must
transport the two independent component-root gauges to these endpoints and
then read the collision residual there, uniformly over arbitrary
multiplicity.

The finite exact profiles calibrate but do not supply that identity.
`atlas-a4-gl5-two-holonomy-readout` proves coefficient `5` on all `202`
packet positions in the fixed 31-point `GL5(F2)` chart.  However
`atlas-a4-classical-two-holonomy-profile` proves the sharp constants `5` on
the inner branch and `21/4` on the outer branch of the natural 15-point
model, with ten outer equality positions.  Hence a branch-independent
version of `(ENDPOINT)` must already permit coefficient at least `21/4` on
classical sectors; the `GL5(F2)` coefficient `5` cannot be promoted to
arbitrary multiplicity.  Finally,
`atlas-a4-outer-extremizer-normal-profile` finds collision-normal lengths
`4` and `2` for the two endpoint cocycles at those equality positions.  This
shows why collision-only word telescoping loses constants, but it is not a
dimension-free operator estimate.

Accordingly this claim remains open.  Its precise missing lemma is a
multiplicity-uniform cross-component endpoint transport/readout inequality
(at minimum enough for `limsup E_2HOL<=1/3`), not another identity for
`t30` and not an improvement of the spherical-chord constant.
