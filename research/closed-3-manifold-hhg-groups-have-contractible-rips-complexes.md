---
rg: 2
id: closed-3-manifold-hhg-groups-have-contractible-rips-complexes
kind: claim
title: If a closed oriented 3-manifold has no Nil, Sol or non-octahedral flat prime factor, its fundamental group has a contractible Rips complex
distinct_from:
  hierarchically-hyperbolic-groups-have-contractible-rips: that is the theorem for all hierarchically hyperbolic groups; this is its 3-manifold case, made unconditional by the Hagen–Russell–Sisto–Spriano classification
---

**ESTABLISHED** (route `closed-3-manifold-hhg-rips-proof`).

Let `M` be a closed oriented 3-manifold with no Nil, Sol or non-octahedral flat manifold
in its prime decomposition. Then `π_1 M` has a finite generating set `T` for which
`P_1(π_1 M, T)` is contractible.

This covers the H²×R and PSL₂(R)~ geometries (central extensions of surface groups),
non-geometric graph manifolds and mixed manifolds, several of which are not CAT(0), and
free products with finite fundamental groups of spherical factors.

**Gap, recorded.** Epstein et al. (*Word Processing in Groups*, Chapter 12; not imported)
show that closed 3-manifold groups are automatic exactly when no prime factor is Nil or Sol.
So among automatic closed oriented 3-manifold groups, the only ones not settled by this
claim are those whose prime decomposition contains a non-octahedral flat manifold. If `M` is itself such a flat
manifold, `π_1 M` is virtually abelian and
`virtually-abelian-groups-have-contractible-rips-complexes` applies. What remains open is a
connected sum of such a flat manifold with another nontrivial factor.
`rips-type-r-closed-under-finite-edge-group-splittings` would close it if the flat factor
were known to be of type R (a fixed generating set at all large scales), which is not
established for non-octahedral crystallographic groups.
