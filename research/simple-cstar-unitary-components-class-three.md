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

Find a simple unital C*-algebra A and unitaries u_1, u_2, v in A whose
triple commutator [u_2, [u_1, v]] is not in U0(A).

Answered (12 Sep 2026, lane ex-unitary-class-three) by the route
class-three-via-spin-bordism-trapping-tower. Run Toms's Grassmannian trapping
tower (arXiv:2609.09535v1) over T^2 x S^3. Its trapped spin-bordism class
reads the eta-squared triple commutator as the Arf-invariant-one torus at
every stage. The argument is complete but not independently reviewed, and it
depends on an unrefereed preprint. Before this, the nonabelian examples all
had class exactly two.

## Attempts

- *Equal-dimension towers.* Dead by
  equal-dimension-ah-component-groups-class-two: blocks with
  dim X <= 2·rank force class at most two, and that includes every LIX-type
  tower.
- *Excess-one tower over T^2 x S^3.* Live. The finite stage has a nonzero
  eta-squared triple commutator (u2-triple-samelson-class-three-stage).
  What is missing is persistence under twisting,
  eta-squared-survives-twisted-excess-tower.
- *Toms trapping tower over T^2 x S^3.* Works:
  simple-ah-algebra-with-class-three-component-group. The base dimension is
  about four times the rank. Spin bordism of the block-diagonal locus
  detects eta squared, and the witness has order two and dies in M_2.

ROUTES

class-three-via-excess-one-eta-tower
