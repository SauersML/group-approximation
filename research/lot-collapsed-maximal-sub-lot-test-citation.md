---
rg: 2
id: lot-collapsed-maximal-sub-lot-test-citation
kind: route
title: Import directed diagrammatic reducibility for collapsed sub-LOTs and its pi_2 consequence
target: lot-collapsed-maximal-sub-lot-test-transfers-asphericity
requires: []
---

Citation import with one elementary step. J. Harlander and S. Rosebrock, *Directed
diagrammatic reducibility*, arXiv:1903.04653v3 (`src.tex`, md5
`a26bde7157a23c2b6f172b3c523fe6a7`), fetched on MSI 2026-09-13.

- l.390--396, Theorem `sLOT`: for `P`, `T`, `S`, `P̄` as in the claim (set-up at
  l.382--388), if `P̄` is compressed and DR directed away from `y` then `P` is DR
  directed away from `S`; "In particular if (1) `W^+(P̄)`, or `W^-(P̄)` is a tree,
  or (2) the Whitehead graph `W(P̄)` does not contain cycles of length less than
  four, then `P` is DR directed away from `S`."
- l.94--99, Theorem `RelPiS` (1): if `P` is DR directed away from the proper
  subset `S` of generators, then `π_2(K(P))` is generated as a `G(P)`-module by
  the image of `π_2(K(P_S))`, where `P_S` is the sub-presentation carried by `S`
  (l.44).

**Elementary step.** `P_S` consists of the relators of `P` whose three letters lie
in `S`. An edge of `P` with both endpoints in `S` lies in `T`, because `T` is a
subtree and paths in a tree are unique; its label is in `S` because `T` is a
sub-LOT. So `P_S` is exactly the LOT presentation of `T`, and `K(P_S) = K(T)`.
If `K(T)` is aspherical, `π_2(K(T)) = 0`, so `π_2(K(P)) = 0` and `K(P)` is
aspherical (a 2-complex with `π_2 = 0` is aspherical).

_Orphan sweep (2026-09-14): this node cited `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
