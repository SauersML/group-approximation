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
- Without asphericity: a cocompact action on a highly connected complex with cell
  stabilizers of type `F_∞`, fed to Brown's criterion. Lane z1-05-artin-direct.
