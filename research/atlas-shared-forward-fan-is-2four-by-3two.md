---
rg: 2
id: atlas-shared-forward-fan-is-2four-by-3two
kind: claim
title: One forward central fan and its adjacent core fan complete to C2^4 semidirect C3^2
artifacts:
  - experiments/atlas_a4_shared_involution_completion.py
  - research/artifacts/atlas-a4-shared-forward-fan-completion.json
distinct_from:
  atlas-one-forward-c3-has-no-standard-gl6-completion: that excludes the entire fourteen-core-plus-collision-plus-forward system in one F2-linear model; this isolates only the forward edge and the core edge sharing its transported involution, and constructs exact complex regular models at every atlas multiplicity.
  a4-coherence-fan-canonically-splits-multiplicity: that describes one regular A4 edge as a fixed qutrit tensor a multiplicity wire; this computes the finite group obtained by gluing the forward and adjacent core qutrit fans over their common involution.
---

Let `r,z` be the commuting first-chart order-three labels on one large packet
component, with `z` in its central `C3`, and let `b` be the second-chart
involution shared by the adjacent core edge and one forward central edge.  The
universal two-fan completion is

```text
C=<r,z,b | r^3=z^3=b^2=[r,z]=(rb)^3=(zb)^3=1>.       (A4-2FAN-1)
```

It is finite of order 144 and has structure

```text
C ~= C2^4 semidirect (C3 x C3).                       (A4-2FAN-2)
```

Its derived subgroup is the elementary abelian `C2^4`, its abelianization is
`C3 x C3`, and its center is trivial.  The subgroup `<r,z>` is `C3 x C3`,
while each of `<r,b>` and `<z,b>` is `A4`.

This completion has exact noncentral complex regular models at every atlas
multiplicity.  Since

```text
20160 = 140*144,
```

put `pi_k=140k Reg(C)`.  Its restrictions are

```text
pi_k|_<r,z> = 2240k Reg(C3 x C3),
pi_k|_<r,b> = pi_k|_<z,b> = 1680k Reg(A4),
pi_k|_<b> = 10080k Reg(C2).                            (A4-2FAN-3)
```

These are exactly the restrictions of `k Reg(A8)` and of the normalized A4
context margins.  After unitarily identifying the fixed first-chart
`C3 x C3` action, `pi_k(b)` has the same balanced involution spectrum as the
second-chart packet label and hence equals `U rho(b) U*` for some unitary `U`.
This common `U` satisfies both A4 edges exactly.  It cannot commute with the
rank-three chart subgroup: otherwise it would fix `rho(b)`, which commutes
with the central `z`, whereas `<z,pi_k(b)>` is `A4`.

Therefore one forward context and its adjacent core context do not yield any
positive semisimple-block or Gram obstruction, even with exact regular A8
margins and arbitrary external multiplicity.  The other core component and
collision `19243` are indispensable.  This claim does not construct a model
for the full fourteen-core-plus-collision-plus-forward system.
