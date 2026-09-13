---
rg: 2
id: every-artin-group-is-type-f-infinity
kind: claim
title: Every finitely generated Artin group is of type F_infinity
---

For every finite set `S` and Coxeter matrix on `S`, the Artin group `A_Γ` has a
`K(A_Γ, 1)` with finitely many cells in each dimension.

This is the positive answer to Zaremsky Problem 1.5
(`zaremsky-1-05-artin-groups-are-type-f-infinity`). The route
`artin-type-f-infinity-via-k-pi-1-conjecture` derives it from the K(π,1)
conjecture, which gives the stronger type F.

## Attempts

- Via the K(π,1) conjecture (`artin-group-k-pi-1-conjecture`): proved for the classes
  listed in the root, in particular every Artin group of dimension at most 3 (the
  dimension-3 case is the preprint arXiv:2509.06914). Open from dimension 4 on.
- Without asphericity (lane z1-05-artin-direct, 2026-09-13; details in
  `research/artifacts/zp-artin-direct-f-infinity-2026-09-13.md`):
  - it reduces to graphs with only finite labels
    (`artin-type-f-n-reduces-to-free-of-infinity-graphs`, route
    `artin-f-infinity-from-free-of-infinity-case`);
  - type `F_{k+1}` holds iff the first nonvanishing homotopy module of the Salvetti
    complex is finitely generated over `ZA` (`artin-type-f-k-plus-1-iff-salvetti-pi-k-fg`),
    so the first open step is finite generation of `π_2(Sal)`, i.e. type `F_3`;
  - Brown's criterion on the Deligne complex or on the Artin complex needs connectivity
    that is equivalent, degree by degree, to that of the Deligne complex
    (`deligne-connectivity-iff-artin-complex-connectivity`), and only simple connectivity
    is known in general.
  No route independent of the K(π,1) conjecture was found.
