---
rg: 2
id: symmetric-selector-schur-residual-packet-proof
kind: route
title: Induce one spin coordinate and transport all residual forms through fixed isomorphisms
target: symmetric-selector-schur-residual-packet
requires:
  - fanizza-schur-menu-has-common-codimension-one-residual
---

Every nondegenerate bilinear pairing on two fifteen-dimensional binary
spaces is left-right equivalent to the standard pairing.  If
`L_x^T B_x R_x=I`, the block map `diag(L_x,R_x)` identifies the alternating
commutator form attached to `B_x` with the standard one.  It therefore lifts
to an isomorphism `phi_x:H->H_x`.  Uniqueness of the `J=-1` spin type makes
the corresponding spin representations exactly intertwined.

The representations `sigma_x` of the base product are irreducible external
tensor products and are pairwise inequivalent.  Their `Sym(X)`-orbit is
transitive.  The stabilizer of `0` fixes the active `H_0` factor pointwise and
merely permutes factors on which `sigma_0` is trivial, so `sigma_0` extends
across that stabilizer.  The little-group form of Clifford theory gives the
irreducibility of its induction, and restriction of the induction to the
base product is the multiplicity-one sum of the sixteen orbit
representations.

On `sigma_x`, exactly one central sign `J_x` acts by `-1`; every other `J_y`
acts trivially.  Equations `(SSP5)--(SSP6)` follow immediately.  If
`B_x=A_x^T C_x` is a chosen left-right factorization relative to the standard
pairing, the preferred coordinate tuples

```text
P_x(u)=phi_x(p(A_x u)),             Q_x(v)=phi_x(q(C_x v))
```

have commutator `J_x^(u^T B_x v)`.  The chosen isomorphism `phi_x` records
exactly this relabelling.  Because the permutation action between factors is
defined through the `phi_x`, the diagonal standard copy is fixed and the
translation from `x` to `x+v` implements the chosen intersector congruence.
This proves the simultaneous residual-router assertion without claiming that
a commutator-changing relabelling is inner in one extraspecial factor.

For `(SSP8)`, permutation of the factor centers gives

```text
tau_v z_i tau_v^(-1)
 =product_(x:x_i=1) J_(x+v)
 =J_all^(v_i) z_i.
```

To expose `tau_v` as a commutator, label every coset of `span(u,v)` by a
square so that its half-turn is addition by `v`.  If `f` is a reflection and
`r` the quarter-turn on every square, then `f` and `rf` are involutions and

```text
[f,rf]=r^2=tau_v.
```

Finally, `Sym(X)` fixes the twisted constant diagonal subgroup `Delta(H)`
pointwise, so these commutator reflections commute with the standard
residual packet.  All exactification constants depend only on the one finite
group `G` and its finite character table, never on the ambient multiplicity.

