---
rg: 2
id: andrew-guerch-hughes-theorem-c-citation
kind: route
title: Apply Andrew--Guerch--Hughes Theorem C
target: automorphism-groups-of-polycyclic-relatively-hyperbolic-groups-satisfy-fjc
requires: []
---

Source: Naomi Andrew, Yassine Guerch, and Sam Hughes,
*Automorphisms of relatively hyperbolic groups and the Farrell--Jones
conjecture*, Mathematische Annalen 395, article 89 (2026),
doi:10.1007/s00208-026-03431-7, Theorem C.

For a one-ended group `G` hyperbolic relative to finitely many conjugacy
classes of virtually polycyclic groups, Theorem C states directly that

```text
Aut(G), Out(G) belong to FJC_X
```

for each `X in {A,K,L}`. Under the paper's convention this is the fibred
conjecture over the virtually cyclic family.

The proof first refines the finite peripheral system so that its members are
non-relatively-hyperbolic. The center of `G` is finite, so `Inn(G)` is
quasi-isometric to `G` and is again relatively hyperbolic with virtually
polycyclic peripherals. Proposition 7.4 establishes `Out(G) in FJC_X`.
Corollary B applied to

```text
1 -> Inn(G) -> Aut(G) -> Out(G) -> 1
```

then establishes `Aut(G) in FJC_X`. The finite-center and refined-peripheral
facts are conclusions used inside the proof, not extra hypotheses. QED
