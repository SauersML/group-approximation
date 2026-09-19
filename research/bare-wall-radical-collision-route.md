---
rg: 2
id: bare-wall-radical-collision-route
kind: route
title: Collide a bare wall with the sofic radical of the free lamp
target: hyperlinear-nonsofic-group
requires: [kun-thom-clifford-radical-phase, bare-relative-wall-exists]
artifacts:
  - notes/FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
---

A unitary `v` in `M intersect pi(Gamma)'` and the homomorphism `pi` together
define a homomorphism of the free lamp
`H=G *_Gamma (Gamma x K)` into `U(M)` by `k |-> v`, since the only relation
crossing the amalgam is `[k,Gamma]=1`.  Its value on the marked word is

```text
Pi(r)=Pi([k,h])=v (pi(h) v^(-1) pi(h)^(-1)),
```

so `Pi(r)!=1` exactly when `v` is a wall.  Kun--Thom centralizer
normalization puts `r` in `Rad_sof(H)` (this is the first half of
`kun-thom-clifford-radical-phase`; the Clifford sign is the second half and
is not used here).  Hence `Pi(H)` is a subgroup of the unitary group of a
Connes-embeddable algebra — so hyperlinear — in which a sofic-radical word
survives, so it is not sofic.

No faithfulness, no anticommutation, and no trace-energy lower bound enter.
