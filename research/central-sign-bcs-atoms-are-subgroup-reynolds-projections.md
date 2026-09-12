---
rg: 2
id: central-sign-bcs-atoms-are-subgroup-reynolds-projections
kind: claim
title: Every Boolean context atom is a central-sign finite-subgroup Reynolds projection
distinct_from:
  boolean-predicate-central-phase-word: That evaluates a Boolean predicate as a central phase in selected finite representations; this realizes each assignment atom itself as an ordinary subgroup average in every representation.
  finite-packet-central-sign-cannot-enforce-nonlinear-support: That rules out deleting forbidden selector characters with a finite packet; this does not delete them and instead exposes their projection mass to a rank actuator.
  subgroup-hecke-hnn-is-a-regular-safe-rank-actuator: That pays a reverse fixed-space gap once subgroup Reynolds projections are supplied; this constructs the Reynolds projection for an arbitrary assignment.
artifacts:
  - notes/NONHYPERLINEAR_FINITE_MEMORY_REYNOLDS_AUDIT.md
  - notes/NONHYPERLINEAR_CHARACTER_REYNOLDS_INTEGRATION_2026-08-24.md
---

Let `x_1,...,x_k` be commuting involutions and let `J` be a central
involution independent of their elementary abelian context group.  For
`a=(a_1,...,a_k) in F_2^k`, put

```text
H_a=<x_i J^(a_i):1<=i<=k> ~= C_2^k,
Q_-=(1-J)/2.
```

Then, in the complex group algebra,

```text
e_(H_a) Q_-
 = product_(i=1)^k (1+(-1)^(a_i)x_i)/2 Q_-.          (CSR1)
```

Thus the right side is exactly the joint spectral projection for assignment
`a` on the `J=-1` sector.  Every forbidden atom of an arbitrary Boolean
constraint is therefore an ordinary finite-subgroup Reynolds projection;
no nonlinear truth-table word or universal rank router is needed to name
that atom.

The identity does not by itself exclude the atom.  The regular representation
contains every such finite-subgroup type, so a successful soundness proof
must still dispose of the compensating sectors forced by subgroup orders.
