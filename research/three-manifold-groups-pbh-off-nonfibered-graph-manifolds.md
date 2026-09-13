---
rg: 2
id: three-manifold-groups-pbh-off-nonfibered-graph-manifolds
kind: claim
title: The fundamental group of a compact 3-manifold lies in the permutational Boone--Higman class unless a prime summand of its orientation cover is a closed graph manifold that is neither non-positively curved nor virtually fibered
distinct_from:
  three-manifold-groups-linear-unless-closed-graph-manifold: that imports linearity over Z for most 3-manifold groups; this is membership in B_A for every compact 3-manifold outside one class, which also needs free products, finite extensions and the fibered case.
  virtually-fibered-3-manifold-groups-satisfy-pbh: that is the fibered input; this is the full case analysis over prime decompositions and geometric types.
  boone-higman-conjecture: that is the universal conjecture; this is the class of compact 3-manifold groups apart from one family of closed graph manifolds.
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

**ESTABLISHED (2026-09-13)** through `three-manifold-pbh-case-analysis-proof`.
Not independently reviewed.

**Statement.** Let `N` be a connected compact 3-manifold. Let `N^+` be `N` if
`N` is orientable and the orientation double cover otherwise, with every
2-sphere boundary component capped by a 3-ball, and let
`N^+ = N_1 # ... # N_r` be its prime decomposition. Suppose no `N_i` is a closed
graph manifold with non-trivial JSJ decomposition that is neither
non-positively curved nor virtually fibered. Then `pi_1(N)` is in `B_A`, the
class of `boone-higman-type-a-class-closed-under-finite-extensions`. So
`pi_1(N)` embeds in a finitely presented simple twisted Brin--Thompson group.

**Exceptional class.** Svetlov proved that non-positively curved graph manifolds
are virtually fibered (Aschenbrenner--Friedl--Wilton, arXiv:1205.0202, l.3327).
So the exception is exactly: closed graph manifolds with non-trivial JSJ
decomposition that are not virtually fibered. Such manifolds exist (AFW, remarks
after `thm:liu11`, citing Luecke--Wu and Neumann). That case is the open node
`nonfibered-closed-graph-manifold-groups-satisfy-pbh`.

**What was known.** The survey arXiv:2306.16356v3, Theorem 5.1, lists (7)
compact 3-manifolds admitting a non-positively curved metric and (8)
finite-volume hyperbolic 3-manifolds. Its Problem 5.3 does not list 3-manifold
groups. Beyond that list:
- **Immediate from known results:** free products and non-orientable manifolds
  (through `B_A`), and closed Seifert fibered manifolds (linear over `Z`).
- **Not reachable by linearity:** virtually fibered graph manifolds that are not
  non-positively curved. No faithful characteristic-zero representation is known
  for them, and the fibered argument transplants BFFHZ Remark 4.1.

No novelty is claimed. The bounded search (the repo, the survey, BFFHZ, BLIW,
AFW, two web queries) found no printed statement of the whole theorem.
