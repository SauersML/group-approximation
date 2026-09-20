---
rg: 2
id: mf-compiler-is-uniform-in-finite-seeds
kind: claim
title: The MF-safe compiler is uniform in its finite seed, not seed-independent
distinct_from:
  mf-safe-finite-presentation-compiler: That states the compiler for a fixed non-MF seed; this retains the seed parameter without identifying positive outputs across seeds.
  arbitrary-forbidden-seed-hereditary-property-switch: That produces recursive switches; this carries their seed parameter through the finite-output compiler.
artifacts:
  - research/artifacts/liu-new-frontiers-2026-09-20.md
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
---

There is a jointly computable map (d,e) -> P_e(d), with d a finite
presentation code and e a program index, such that

```
e in FIN  =>  Carrier(d) embeds in Carrier(P_e(d)),
e in INF  =>  R_e(d):=Carrier(P_e(d)) is regularly operator-MF.
```

On INF the bridge Q_e(d) is abstractly B3(1), but the actual Higman
host H_e(d), Mikhailova subgroup and rope retain their presentation
parameter d. No isomorphism between R_e(d) and R_e(d') is asserted.
Uniformity of the algorithm is not seed-independence of the outputs.

The FIN embedding is pointwise existential and uses a last-event cutoff
of the recursive switch. Only output presentation codes and the bridge
construction data are uniformly computed. No computable family of seed
homomorphisms on all indices is asserted; that stronger requirement is
excluded by the uniform-seed-map firewall.
