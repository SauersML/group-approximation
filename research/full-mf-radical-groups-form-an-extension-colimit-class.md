---
rg: 2
id: full-mf-radical-groups-form-an-extension-colimit-class
kind: claim
title: Full-MF-radical groups are closed under quotients, extensions, and countable colimits
artifacts:
  - research/full-mf-radical-groups-form-an-extension-colimit-class-proof.md
---

Let

```text
Z_MF={G countable : Rad_MF(G)=G}.
```

Then `Z_MF` is closed under:

1. arbitrary homomorphic images;
2. group extensions: if `1->N->G->Q->1` is exact and `N,Q in Z_MF`, then
   `G in Z_MF`;
3. every countable group colimit of a diagram taking values in `Z_MF`;
4. free products, amalgamated free products whose vertex groups lie in
   `Z_MF`, finite products, countable restricted sums, and graph products;
5. directed unions of full-radical subgroups.

Equivalently, `Z_MF` is the zero class of the MF reflector: it is an
extension-closed radical class as well as the colimit kernel of the
localization `R_MF`.

Every nontrivial quotient of a group in `Z_MF` is again non-MF and has no
nontrivial homomorphism to an MF group.
