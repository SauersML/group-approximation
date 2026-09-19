---
rg: 2
id: supporting-choi-component-does-not-force-primal-motion
kind: claim
title: A norm-attaining Choi separator component need not produce primal motion in that component
distinct_from:
  centered-gap-is-on-a-tree-or-forces-tree-motion: that isolates a large centered closing component for the concrete triangle separator; this gives a finite Choi countermodel to the proposed generic dual-to-primal inference from that component.
  scalar-tree-perturbations-linearly-control-closing-face: that constrains the restrictions of each primal ucp triangle map; this shows a large dual component need not select any primal map to which that constraint applies nontrivially.
  exhausting-ideal-reservoirs-have-lift-or-quotient-separator: that constructs a normalized supporting functional from persistent distance; this shows that even choosing the distance-normalized functional and a closest feasible point supplies no componentwise primal displacement.
---

**ESTABLISHED (finite Choi countermodel).**  There is a finite-dimensional
operator system `E`, a finite-dimensional codomain, a closed convex face `K`
of its ucp Choi set, a target ucp map `psi`, a distinguished feasible scalar
map `e`, and a norm-one distance separator `ell` such that

```text
ell(psi)-sup_(phi in K)ell(phi)=dist(psi,K)>0,              (SCP1)
```

the separator attains the normal-cone equality at **every** closest point of
`K`, and its entire centered value is on one named coordinate, but

```text
phi(closing coordinate)=e(closing coordinate)
                    for every phi in K.                    (SCP2)
```

Thus neither closest-point selection, norm-attaining Hahn--Banach
normalization, nor complementary slackness forces a primal closing
displacement from a large centered closing component of the separator.

The countermodel is the state Choi simplex of `E=C^3`.  It already occurs in
scalar codomain, so no matrix-size or nonclosed-image issue is involved.

**Consequence for the triangle.**  The implication

```text
c_13>=2delta/3
  ==> some closest liftable ucp comparison has r_13>=r(delta)             (SCP3)
```

cannot follow from finite-dimensional Choi duality and separator
normalization alone.  A proof of `(SCP3)` for the triangle would need an
additional triangle-specific transversality/error-bound property of the
liftable Choi image.  Once such an `r(delta)` is available,
`scalar-tree-perturbations-linearly-control-closing-face` converts it to tree
motion at least `r(delta)/C_Delta`.

Proof: `three-point-choi-face-no-primal-motion`.

DERIVATION
three-point-choi-face-no-primal-motion
