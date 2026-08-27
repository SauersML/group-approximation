---
rg: 2
id: atlas-a4-two-holonomy-reflection-energy-ceiling
kind: claim
title: The A4 packet and 19243 keep the core-reflection energy at most one third
distinct_from:
  atlas-a4-parabolic-c3-bridge-energy-ceiling: that separately budgets the two packet S3 letters, the central C3 letter, and the collision involution; this asks only for the combined core holonomy c=hk and collision-C3 reflection a=zb.
---

Let `U_n` satisfy the normalized exact-regular A4 packet hypotheses and
`q_19243(U_n)->1`.  With

```text
c=hk,
a=zb,
E_2HOL(U)=2 delta_U(c)^2+delta_U(a)^2
```

as in `atlas-t30-is-one-parabolic-c3-bridge`, prove

```text
limsup_n E_2HOL(U_n)<=1/3.                             (A4-2HOL-CEIL)
```

This is sufficient, not asserted established.  The exact two-holonomy
factorization and spherical chord bound give the strict rational estimate

```text
limsup_n x30(U_n)^2<=338/729<1/2.
```

The target is deliberately expressed in the two gauge-invariant combinations
which the exact subgroup geometry singles out.  It does not separately ask
the two disconnected packet components to synchronize `h` and `k`, nor does
it separately decode `z` from the collision involution `b`.

## Attempts

- After the `K_(2,2) disjoint_union K_(2,4)` tree gauge, identify `c=hk` with
  the relative phase between the two component root gauges and `a=zb` with
  the 19243 residual in the commuting `S3` partner.  Seek a two-variable
  connection-Laplacian or trace inequality rather than reconstructing four
  individual letter defects.
- `atlas-two-holonomy-endpoint-localization` makes the required compiler map
  precise: `h` lies on the `K_(2,2)` component, `k,z` lie on `K_(2,4)`, and
  `b` is collision-only.  Thus `c,a` are cross-component endpoint products,
  not individual rectangle variables.  The four rectangles first remove
  internal cycle gauge; two component-root transports and the collision
  endpoint still have to be decoded.
- The natural threshold is non-strict.  Curvature of the unitary sphere gives
  a fixed gap of `1/2-338/729=53/1458` after the bridge.
- The full spherical threshold is actually
  `12 sin^2(pi/18)>1/3`; the rational `1/3` is retained as the clean packet
  budget.
- `atlas-a4-classical-two-holonomy-profile` exhausts the natural 15-point
  classical sector.  The sharp readout coefficient is `5` on the inner
  automorphism branch but `21/4` on the outer branch; ten outer positions
  violate coefficient `5`.  Thus the sharp `5` observed in the 31-point GL5
  screen is not a universal identity and cannot be promoted without retaining
  additional branch or multiplicity information.

## Conditional-expectation and tree-gauge audit

A direct collapse onto either packet-component commutant cannot prove the
claim.  For a finite subgroup `H` and its Reynolds expectation

```text
E_H(X)=|H|^-1 sum_(g in H) rho(g)Xrho(g)^*,
```

orthogonality gives the exact identity

```text
|H|^-1 sum_(g in H) ||[X,rho(g)]||_2^2
 =2 ||X-E_H(X)||_2^2.                                 (REYNOLDS)
```

Let `K ~= S3` be the collision subgroup from
`atlas-a4-19243-s3xs3-localization`.  It is contained in the large component
`H_18 ~= S3 x C3`.  But `atlas-19243-relation-forces-s3-distance` proves,
under the same hypothesis `q_19243(U_n)->1`, that

```text
liminf_n dist_2(U_n,rho(K)')^2 >=1/32.
```

Since `rho(H_18)'` is contained in `rho(K)'`, the same sequence satisfies

```text
liminf_n dist_2(U_n,rho(H_18)')^2 >=1/32.             (LARGE-FAR)
```

Thus collision does not make the relative frame component-central; it forces
the opposite behavior on its `S3` factor.  In particular, applying
`(REYNOLDS)` to seek `dist_2(U_n,rho(H_18)')->0` is incompatible with the
collision relation and cannot yield the desired upper bound.  An expectation
argument would instead have to project the **endpoint cocycles** associated
with `c` and `a`, after retaining their relative gauge, rather than project
`U_n` onto a component commutant.

There is also a precise information loss in the four-rectangle normal form.
`atlas-a4-packet-four-rectangle-normal-form` gauges the two disconnected
components independently.  Its four rectangle holonomies are invariant under
the two independent component-root gauge choices.  By
`atlas-a4-19243-s3xs3-localization`, the collision polynomial uses only the
large component `H_18` and the collision involution `b`; it contains no
`H_6` letter.  Hence, at the level of the abstract edge-message normal form,
changing the `H_6` root gauge leaves all four rectangles and the collision
residual unchanged, while changing the cross-component endpoint represented
by `c=hk`.

This is a no-go only for a compiler which discards the common relative frame
and keeps just the four gauge-invariant rectangles plus the collision
polynomial.  Such data cannot determine `delta_U(c)`.  It is not a
counterexample to `(A4-2HOL-CEIL)`, because an arbitrary independent root-gauge
change need not lift to a single unitary `U` satisfying all thirty shifted
centralizer-product constraints.  The minimal missing input is exactly that
liftability constraint: a dimension-free inequality transporting the common
`U` across the two component roots before taking the two endpoint Reynolds
energies.

The finite profiles remain consistent with this diagnosis.  On exact packet
positions the 31-point `GL5(F2)` chart has the sharp readout

```text
E_2HOL <=5 ||q_19243-1||_2^2,
```

whereas the 15-point outer automorphism branch requires the sharp coefficient
`21/4`.  Therefore any branch-blind lifted endpoint inequality of this form
must allow a coefficient at least `21/4`; coefficient `5` cannot arise from a
representation-independent conditional-expectation contraction.  These
finite constants do not prove the asymptotic ceiling, since their models have
nonzero collision defect and contain no arbitrary matrix-valued multiplicity
holonomy.

Accordingly the claim remains open.  The direct component-expectation route is
rigorously obstructed, and the exact missing lemma is a common-frame,
cross-component endpoint transport inequality; the four rectangle invariants
alone do not contain it.
