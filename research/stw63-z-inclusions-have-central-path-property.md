---
rg: 2
id: stw63-z-inclusions-have-central-path-property
kind: claim
title: Every Jiang--Su inclusion has the controlled central path property
---

For every unital C-star algebra `B` and unital embedding `phi:Z->B`, the
central path property stated in
`approximate-to-asymptotic-via-central-paths` holds: sufficiently
`phi(G)`-central unitaries contract to `1` through uniformly
`phi(F)`-central paths, for arbitrary prescribed finite `F` and tolerance.

## Attempts

- Exact relative-commutant unitaries in a nontrivial connected component are
  the first obstruction.  A proof must show that the surrounding approximate
  commutants erase those components, or explain how exact-commutant unitaries
  can correct transition classes before contraction.
- `K_1(Z)=0` is not enough: the transition unitaries lie in `B`, and their
  relevant topology is relative to `phi(Z)`, not the unitary group of `Z`.
- In regular absorbing targets, basic homotopy lemmas and central-sequence
  absorption are natural sources of controlled paths.  The missing issue is
  uniformity with no regularity assumption on `B`.
- A weaker hinge sufficient for STW LXIII would only contract transition
  unitaries arising from two increasingly accurate implementers, rather than
  every approximately central unitary.  No intrinsic characterization of
  that smaller subset is currently available.
