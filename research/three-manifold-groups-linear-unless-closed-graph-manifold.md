---
rg: 2
id: three-manifold-groups-linear-unless-closed-graph-manifold
kind: claim
title: Fundamental groups of aspherical compact orientable 3-manifolds are linear over Z except possibly for closed graph manifolds with non-trivial JSJ decomposition that are not non-positively curved
distinct_from:
  char-zero-linear-groups-satisfy-permutational-boone-higman: that puts every finitely generated characteristic-zero linear group in B_A; this imports which 3-manifold groups are known to be such linear groups.
  cubulated-hyperbolic-groups-are-virtually-special: that is virtual specialness for hyperbolic cubulated groups; this is linearity over Z for 3-manifold groups, most of which are not hyperbolic.
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

**ESTABLISHED (literature import)** through
`three-manifold-groups-linearity-citation`.

Let `N` be a compact, orientable, aspherical 3-manifold. Then `pi_1(N)` is
linear over `Z` in each of the following cases:

1. `N` has non-empty boundary;
2. `N` is Seifert fibered;
3. `N` is closed and is not a graph manifold;
4. `N` is a closed graph manifold that is non-positively curved.

Also:

5. fundamental groups of closed orientable surfaces are linear over `Z`;
6. virtually polycyclic groups are linear over `Z`.

Conventions (from the source): a *graph manifold* is a compact orientable
irreducible 3-manifold with empty or toroidal boundary all of whose JSJ
components are Seifert fibered; `N` is *non-positively curved* if its interior
admits a complete non-positively curved Riemannian metric.

**Not covered.** Closed graph manifolds with non-trivial JSJ decomposition that
are not non-positively curved. Douba, arXiv:2101.06797, l.206 of the TeX: "At
the time of writing of this article, it is not known if a single non-NPC graph
manifold without Sol geometry admits a faithful finite-dimensional linear
representation over a field of characteristic zero." Some of them are not
linear over any field of positive characteristic and have no faithful
finite-dimensional unitary representation (same paper: the abstract, for
graph manifolds with one JSJ torus and product blocks; l.206, Button with Leeb,
for positive characteristic and every non-NPC graph manifold).

**Scope.** Nothing is reproved. The survey arXiv:2306.16356v3, Theorem 5.1(7),
already lists the non-positively curved case as satisfying Boone--Higman.
