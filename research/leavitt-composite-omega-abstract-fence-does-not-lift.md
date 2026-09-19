---
rg: 2
id: leavitt-composite-omega-abstract-fence-does-not-lift
kind: claim
title: The universal-gate fence for composite Omega transport violates two short Leavitt packet relations
artifacts:
  - research/leavitt-composite-omega-abstract-fence-does-not-lift-proof.md
distinct_from:
  leavitt-degree-four-affine-omega-candidate: that constructs the first affine orbit system; this audits a strengthened composite-gate version against an abstract countermodel and the actual packet relations.
  leavitt-omega-has-an-explicit-distorted-target: that proves the target commutator is nontrivial; this determines why the apparent abstract fence does not yet preserve a full coefficient copy.
---

For the composite source and target gates

```text
b=r^2ar^(-2),       d=p^2cp^(-2),
```

there is an abstract four-cell countermodel satisfying the orbit relators and
`[a,b]=1` while retaining `[c,d] !=1`.  It cannot be promoted directly to a
Leavitt-packet countermodel: setting `r_0=1,p_0=P` violates `r=qp,q^2=1`,
and its assignments for `c_0,e_0` violate the exact root commutation
`[c,e]=1`.

Thus the source commutation and conjugate-gate definitions alone do not
transport the relation, but a full-copy Bass--Serre fence has not been
constructed either.  The first unresolved input is precisely the additional
within-copy packet structure.
