---
rg: 2
id: simple-cstar-unitary-components-class-three
kind: claim
title: Some simple unital C*-algebra has a unitary component group of nilpotency class at least three
root: true
distinct_from:
  stw59-nonabelian-unitary-component-groups: That realizes nonabelian component groups of class exactly two, as central extensions of K1; this asks for a nonzero triple commutator.
  u2-triple-samelson-class-three-stage: That gives class three for the nonsimple algebra C(T^2 x S^3, M_2); this asks for it in a simple algebra.
artifacts:
  - research/artifacts/stw59-samelson-orders-and-wedged-arms-2026-09-11.md
---

**OPEN.** Find a simple unital C*-algebra A and unitaries u_1, u_2, v in A
whose triple commutator [u_2, [u_1, v]] is not in U0(A).

The present nonabelian examples all have class exactly two.

## Attempts

- *Equal-dimension towers.* Dead by
  equal-dimension-ah-component-groups-class-two: blocks with
  dim X <= 2·rank force class at most two, and that includes every LIX-type
  tower.
- *Excess-one tower over T^2 x S^3.* Live. The finite stage has a nonzero
  eta-squared triple commutator (u2-triple-samelson-class-three-stage).
  What is missing is persistence under twisting,
  eta-squared-survives-twisted-excess-tower.

ROUTES

class-three-via-excess-one-eta-tower
