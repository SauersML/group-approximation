---
rg: 2
id: finite-type-restriction-incidence-atlas-for-nonce-bcs
kind: claim
title: Realize a no-CE BCS by zero-defect restriction incidence of finite types
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that permits arbitrary algebraic projections and leaves shared-marginal equality as a group-ring equation; this restricts every context atom to one transported finite type and replaces each equality by the explicit restriction-intersection defect.
  term-pairing-does-not-bypass-signed-hecke-holonomy: that pairs coefficients and then must restore star and idempotence; here every summand is already a projection and equality is certified by one faithful positive L2 identity.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that absorbs one finite arrow or bisection at a time; this requires a many-to-many restriction incidence whose cumulative support contains a load-bearing non-groupoid cycle.
---

Fix the finite BCS `B` supplied by `mipstar-bcs-tracial-nonru-exists`.
Construct a finitely presented group `Gamma`, a finite subgroup
`K<=Gamma`, an irreducible `pi in Irr(K)` with `dim(pi)>1`, and

```text
q=z_(K,pi)!=0.
```

For every context `c`, choose a nonempty support `S_c subseteq R_c`.
For each `a in S_c`, choose a finite subgroup `H_(c,a)<=Gamma`, an
irreducible type `rho_(c,a)`, and a word `g_(c,a)`, and set

```text
p_(c,a)=g_(c,a) z_(H_(c,a),rho_(c,a)) g_(c,a)^(-1).    (FTI1)
```

Require, in each context,

```text
p_(c,a)p_(c,b)=0  (a!=b),       sum_(a in S_c)p_(c,a)=q. (FTI2)
```

For a shared variable `x in U_c intersect U_d`, put

```text
P_(c,x,+)=sum_(a in S_c:a_x=+1)p_(c,a),
P_(d,x,+)=sum_(b in S_d:b_x=+1)p_(d,b).                 (FTI3)
```

Require the explicit right side of `(FTO2)` for the two families in
`(FTI3)` to be zero. Equivalently, the finite subgroup intersections and
restriction multiplicities must satisfy

```text
||P_(c,x,+)-P_(d,x,+)||_2^2=0                           (FTI4)
```

for every shared incidence.

The target is genuinely narrower than an arbitrary signed-Hecke atlas: all
projection, orthogonality, and overlap checks are finite-type restriction
data. It is nevertheless sufficient. Faithfulness turns `(FTI4)` into
literal equality, so

```text
V_x=2P_(c,x,+)-q
```

is context-independent and the PVM `(p_(c,a))_(a in S_c)` kills every
forbidden assignment.

Any solution automatically crosses the known fences. By
`no-ce-hecke-host-needs-an-fd-invisible-type`, every finite-dimensional
representation of `Gamma` annihilates `q`. The large-intersection and
row-column-capacity theorems rule out sparse single-type attachments.
`clean-face-finite-type-packing-is-quadratically-bounded` excludes the
central-sign clean star, while
`central-type-sum-equality-is-intersection-readable` proves that using one
central finite chart on each side makes every common marginal a literal
intersection projection. Finally,
`finite-projective-sector-groupoids-have-conjugate-absorbers` excludes
finitely many single packet arrows or bisections. Thus at least one cycle
must use atom-specific chart groups with non-clean intersections or a
genuinely noncentral multipath restriction sum; a finite graph of finite
groups, graph product, or finite biunitary packet does not qualify.
