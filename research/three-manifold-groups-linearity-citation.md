---
rg: 2
id: three-manifold-groups-linearity-citation
kind: route
title: Import linearity over Z of 3-manifold groups from the Aschenbrenner--Friedl--Wilton survey
target: three-manifold-groups-linear-unless-closed-graph-manifold
requires: []
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

Citation import. Source: M. Aschenbrenner, S. Friedl, H. Wilton, *3-manifold
groups*, arXiv:1205.0202, TeX source
`3-manifold-groups-new-version-032613.tex`, fetched on MSI 2026-09-13. Line
numbers refer to that file; the verbatim passages are in the artifact.

1. **Non-empty boundary.** Corollary `cor: Non-toroidal properties` (l.2738--2743):
   "Let N be a compact, orientable, aspherical 3-manifold with non-empty
   boundary. Then (1) π1(N) is linear over Z".
2. **Seifert fibered.** Theorem `thm:Seifert linear` (l.3702--3704): "Let N be a
   Seifert fibered manifold. Then π1(N) is linear over Z." The proof, due to
   Boyer, is printed at l.3708--3787.
3. **Closed, not a graph manifold.**
   - Leeb, Theorem `thm:leeb` (l.2613--2616): "Let N be an irreducible
     3-manifold with empty or toroidal boundary. If N is not a closed graph
     manifold, then N is non-positively curved."
   - Theorem `thm:npcvs` (l.2659--2662): for compact orientable aspherical `N`
     with empty or toroidal boundary, "π1(N) is virtually special if and only
     if N is non-positively curved."
   - Virtually special implies linear over `Z`. Special groups are subgroups of
     RAAGs (Corollary `cor: HW special`, from Haglund--Wise). RAAGs are linear
     over `Z` ((G.24), Hsu--Wise). Linearity over a ring passes to finite-index
     overgroups ((H.lineargreen), l.3268--3270, by induction of the
     representation). AFW use exactly this chain in the proof of
     `cor: Non-toroidal properties`, l.2750.
4. **Non-positively curved graph manifolds.** Liu, Theorem `thm:liu11`
   (l.2620--2622): "Let N be an aspherical graph manifold. Then π1(N) is
   virtually special if and only if N is non-positively curved." Then the chain
   in item 3.
5. **Surface groups.** l.3742 and l.3748: "surface groups are linear over Z".
6. **Virtually polycyclic groups.** l.2046: "Groups which are virtually
   polycyclic are linear over Z by the Auslander--Swan Theorem".

Definitions of graph manifold and non-positively curved: l.2606--2609.
