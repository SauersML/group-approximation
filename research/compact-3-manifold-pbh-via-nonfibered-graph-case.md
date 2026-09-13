---
rg: 2
id: compact-3-manifold-pbh-via-nonfibered-graph-case
kind: route
title: Combine the case analysis with the non-virtually-fibered graph manifold case
target: compact-3-manifold-groups-satisfy-pbh
requires:
  - three-manifold-groups-pbh-off-nonfibered-graph-manifolds
  - nonfibered-closed-graph-manifold-groups-satisfy-pbh
  - boone-higman-type-a-class-closed-under-finite-extensions
  - aut-free-groups-satisfy-permutational-boone-higman
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

Run `three-manifold-pbh-case-analysis-proof` unchanged. In its last sub-case, a
closed graph manifold that is neither non-positively curved nor virtually fibered
is not virtually fibered, so its group is in `B_A` by
`nonfibered-closed-graph-manifold-groups-satisfy-pbh`. Every prime summand then
lands in `B_A`. BFFHZ Corollary F (free products, in
`aut-free-groups-satisfy-permutational-boone-higman`) and closure under
finite-index overgroups (part 2 of
`boone-higman-type-a-class-closed-under-finite-extensions`) finish the argument.
