---
rg: 2
id: hierarchically-hyperbolic-groups-have-contractible-rips
kind: claim
title: Every hierarchically hyperbolic group, torsion included, has a contractible Rips complex
distinct_from:
  torsion-free-hhg-subgroups-have-contractible-rips-complexes: that gives contractible Rips complexes only for torsion-free finite-index subgroups; this gives them for the hierarchically hyperbolic group itself, for example the full mapping class group with its torsion
  coarsely-injective-groups-with-torsion-have-contractible-rips: that is the general theorem for proper cobounded actions on coarsely injective spaces; this is its application to hierarchically hyperbolic groups
---

**ESTABLISHED** (route `hhg-with-torsion-rips-proof`).

Let `H` be a hierarchically hyperbolic group. Then there is a finite generating set `T` of
`H` such that the Rips complex `P_1(H, T)`, the clique complex of `Cay(H, T)`, is
contractible. In the equivalent formulation of
`rips-complex-of-a-group-is-a-flag-cayley-complex`, some Rips complex of `H` is
contractible.

Examples (as recorded in `hierarchically-hyperbolic-groups-are-coarsely-injective` and
`closed-3-manifold-groups-hhg-classification`):

- mapping class groups of surfaces, with their torsion;
- the Hughes–Valiunas hierarchically hyperbolic group that is not biautomatic, hence not
  Helly, so `helly-groups-have-contractible-rips-complexes` does not apply;
- fundamental groups of closed oriented 3-manifolds with no Nil, Sol or non-octahedral flat
  manifold in the prime decomposition.

**Relation to `automatic-groups-have-contractible-rips-complexes`.** Mapping class groups
are automatic (Mosher, *Mapping class groups are automatic*, Ann. of Math. 142 (1995)),
and so are the 3-manifold groups above (Epstein et al., *Word Processing in Groups*,
Chapter 12). These are background facts, not prerequisites of this claim, and they are
not imported here. So this claim adds these automatic groups with torsion to the known
cases of the open claim. The torsion condition of
`automatic-groups-conjugate-finite-p-subgroups-into-a-ball` then holds for them by
`contractible-rips-conjugates-p-subgroups-into-balls`.
