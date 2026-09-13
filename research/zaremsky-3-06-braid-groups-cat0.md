---
rg: 2
id: zaremsky-3-06-braid-groups-cat0
kind: claim
title: "Zaremsky Problem 3.6 resolved: are braid groups CAT(0)?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3 ("Matrix groups,
braid groups, etc"), Problem 6, verbatim:
"Are braid groups CAT(0)? Even without requiring cocompactness this is
unknown."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-06-by-yes` requires `every-braid-group-is-cat0`.
- **No**: `zaremsky-3-06-by-no` requires `some-braid-group-is-not-cat0`.

Never write a `requires: []` route into this claim.

## Reading

`B_n` is the Artin braid group on `n` strands,
`<s_1, ..., s_{n-1} | s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}, s_i s_j = s_j s_i for |i-j| >= 2>`.
A group is *CAT(0)* when it acts geometrically (properly, cocompactly, by
isometries) on a complete CAT(0) metric space. "Braid groups are CAT(0)"
means that every `B_n` is CAT(0); "no" means that some `B_n` is not.

Known, per the abstracts of the papers (import nodes land after the theorem
statements are read in full):

- `B_n` is CAT(0) for `n <= 6`: Haettel–Kielak–Schwer, arXiv:1304.5990
  (Geom. Dedicata 182 (2016) 263), building on Brady–McCammond,
  arXiv:0909.4778 (Algebr. Geom. Topol. 10 (2010) 2277–2314), who did `n = 5`.
- `B_7` is CAT(0): Jeong, arXiv:2009.09350 (2020), "by elaborating on the
  argument of Haettel, Kielak and Schwer".
- `B_n` is not virtually cocompactly cubulated for `n >= 4`: Haettel,
  arXiv:1509.08711. So a CAT(0) model cannot be a cube complex.

So the question is open exactly for `n >= 8`.

Zaremsky's second sentence names a weaker question: a proper isometric action
with no cocompactness. Which spaces count changes the answer, so the graph
keeps the readings apart:

- `every-braid-group-acts-properly-on-a-proper-cat0-space`: proper
  (locally compact) CAT(0) spaces, the setting of CAT(0) groups. The yes
  answer implies it; its negation `some-braid-group-has-no-proper-cat0-action`
  implies the no answer.
- Complete CAT(0) spaces that are not locally compact form a different
  question. Hilbert spaces are among them, so the Haagerup property for
  braid groups (Problem 3.7, `zaremsky-3-07-braid-groups-haagerup`) would
  give proper actions on them without touching the cocompact question.

## Attempts

- 2026-09-13, lane z3-06-braid-cat0. Main route: the Brady–McCammond
  orthoscheme complex of the noncrossing-partition lattice `NC_n` is a compact
  `K(B_n, 1)`; its universal cover is CAT(0) exactly when the link condition
  holds, which reduces to finitely many checks for each `n`. The known cases
  `n <= 7` embed diagonal links into spherical buildings of type A. What breaks
  at `n = 8` is the sharpest open point; the lane is reading the two papers to
  locate it.
