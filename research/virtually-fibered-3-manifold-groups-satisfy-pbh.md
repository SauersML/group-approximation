---
rg: 2
id: virtually-fibered-3-manifold-groups-satisfy-pbh
kind: claim
title: Every group commensurable with a surface-by-cyclic group, in particular every virtually fibered closed 3-manifold group, lies in the permutational Boone--Higman class
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that covers free-by-cyclic groups; this covers extensions of closed surface groups by Z, whose fibres are not free.
  punctured-surface-mcgs-satisfy-permutational-boone-higman: that is the host, mapping class groups of punctured surfaces; this is the class of surface-by-cyclic groups placed inside such a host.
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is the open case of closed-surface mapping class groups; this uses only the once-punctured mapping class group, which is known.
  three-manifold-groups-linear-unless-closed-graph-manifold: that is linearity over Z; this is membership in B_A for virtually fibered 3-manifolds, including fibered graph manifolds that are not non-positively curved, whose groups are not known to be linear in characteristic zero.
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

**ESTABLISHED (2026-09-13)** through `virtually-fibered-3-manifold-pbh-proof`.
Not independently reviewed.

**Statement.** Let `Sigma` be a closed orientable surface and `phi` an automorphism
of `pi_1(Sigma)`. If a group `G` has a finite-index subgroup isomorphic to
`Z ⋉_phi pi_1(Sigma)`, then `G` is in `B_A`, the class of
`boone-higman-type-a-class-closed-under-finite-extensions`. So `G` embeds in a
finitely presented simple group.

**3-manifold form.** Let `N` be a closed orientable 3-manifold with a finite
cover that fibres over the circle. Then `pi_1(N)` is in `B_A`.

**Why it matters.** Some closed graph manifolds with non-trivial JSJ
decomposition fibre but are not non-positively curved (Aschenbrenner--Friedl--Wilton,
arXiv:1205.0202, remarks after `thm:liu11`). For those, no faithful
finite-dimensional representation in characteristic zero is known (Douba,
arXiv:2101.06797, l.206), so the linear route of
`three-manifold-groups-linear-unless-closed-graph-manifold` does not reach them.

**Credit.** The argument is the free-by-cyclic argument of BFFHZ Remark 4.1
(arXiv:2503.21882v2, l.667--671), with `Aut(F_n)` replaced by
`Aut(pi_1(Sigma)) = Mod^±(S_(g,1))`. No novelty is claimed.
