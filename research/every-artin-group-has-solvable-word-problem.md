---
rg: 2
id: every-artin-group-has-solvable-word-problem
kind: claim
title: Every Artin group has solvable word problem
distinct_from:
  artin-groups-satisfy-boone-higman: that is the Boone-Higman problem over Artin groups that already have solvable word problem; this is solvability of the word problem itself for every Artin group, the hypothesis that problem assumes.
  every-artin-group-is-type-f-infinity: that is a finiteness property of classifying spaces; this is an algorithmic property, and neither is known to imply the other.
---

**OPEN.** For every finite Coxeter graph `Γ`, the Artin group `A_Γ` has solvable word
problem.

Recorded as open by Belk–Bleak–Matucci–Zaremsky, arXiv:2306.16356, footnote 10 (ar5iv
rendering): "It is an open question whether all Artin groups have solvable word
problem [Charney, *Problems related to Artin groups*, Problem 10], but this is known
for several large classes, such as right-angled Artin groups ... and Artin groups of
spherical or Euclidean type."

It is equivalent to the yes answer to Zaremsky Problem 3.8. See
`every-artin-twisted-brin-thompson-group-embeds-in-fp-group` and the route
`artin-solvable-word-problem-from-twisted-bt-fp-hosts`.

## Attempts

- **Class by class, as in the literature.**
  - Garside structures: spherical type; euclidean type through supergroups
    (McCammond–Sulway, arXiv:1312.7770, Theorem D); rank three through dual structures
    (Delucchi–Paolini–Salvetti, arXiv:2206.14518, Theorem 7.4).
  - Helly and systolic geometry: type FC (Huang–Osajda, arXiv:1904.09060), large type
    (arXiv:1706.05473), dimension ≤ 2 through the conjugacy problem (arXiv:1710.05157,
    Corollary 1.3(2)).
  - Rewriting: Artin groups with no relation of length 3 (Blasco-García, Cumplido and
    Morris-Wright, arXiv:2204.03523; abstract read, body not read).
  - **The gap:** rank at least 4, not FC type, not 2-dimensional, not euclidean, and
    some label equal to 3.
- **Through an explicit finitely presented host of `AV_A`** (artifact
  `research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md` §6). This is
  equivalent in strength; it is a construction strategy, not a reduction.
- Not attempted by lane z3-08-artin-bt-embed beyond the reduction.
