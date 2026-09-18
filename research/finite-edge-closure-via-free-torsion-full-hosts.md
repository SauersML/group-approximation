---
rg: 2
id: finite-edge-closure-via-free-torsion-full-hosts
kind: route
title: Put the vertex group in a full Cantor host where both edge groups act freely, conjugate them by gluing fundamental domains, and absorb the edge by a centralizing HNN extension
target: pbh-closed-under-finite-edge-graphs-of-groups
requires:
  - b-a-groups-embed-in-full-hosts-with-free-torsion
  - finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a
  - pbh-finite-edge-closure-equivalences
---

By `pbh-finite-edge-closure-equivalences`, it suffices to realize form 2, HNN extensions
`G*_θ` over finite subgroups `C_1, C_2`.
- By `b-a-groups-embed-in-full-hosts-with-free-torsion`, `G` embeds in a full
  clopen-transitive `D ∈ B_A` in which `C_1` and `C_2` act freely.
- Apply `finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a` to the one-vertex,
  one-loop graph of groups. `∎`
