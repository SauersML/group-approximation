---
rg: 2
id: standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups
kind: claim
title: "The classical groups of type F_n but not F_{n+1} embed in groups of type F_infinity: in type-F groups for Bieri-Stallings and Bestvina-Brady, in GL_n(Z[1/p]) for Abels"
artifacts:
  - research/artifacts/zp-review-topology-2026-09-13-part1.md
---

Each classical family of groups of type `F_n` but not `F_{n+1}` is a subgroup
of a group of type `F_∞`, by construction. So none of them witnesses the
negative answer `some-type-fn-group-embeds-in-no-type-fn-plus-1-group` to
Zaremsky Problem 1.1. They show that the finiteness gap in the problem occurs,
and that it is not a witness by itself.

- **Bieri--Stallings groups.** `SB_n` is the kernel of the map
  `F^{(1)} x ... x F^{(n)} -> Z` from a product of `n` nonabelian free groups
  that sends every free generator to `1` (Stallings 1963 for `n = 3`; Bieri,
  *Homological dimension of discrete groups*, QMC Notes 1976). `SB_n` is of
  type `F_{n-1}` but not of type `FP_n`. It is a subgroup of the product of
  free groups, which has a finite `K(π,1)` (a product of finite graphs), so it
  is of type `F`.

- **Bestvina--Brady groups.** For a finite flag complex `L`, `BB_L` is the
  kernel of the map from the right-angled Artin group `A_L` sending each
  standard generator to `1` (Bestvina--Brady, *Morse theory and finiteness
  properties of groups*, Invent. Math. 129 (1997)). `BB_L` is of type `F_n` iff
  `L` is `(n-1)`-connected. It is a subgroup of `A_L`, whose Salvetti complex
  is a finite `K(π,1)`, so `A_L` is of type `F`.

- **Abels' groups.** `A_n(Z[1/p])` is the group of upper triangular `n x n`
  matrices over `Z[1/p]` whose `(1,1)` and `(n,n)` entries are `1` and whose
  other diagonal entries are powers of `p` (Abels, LNM 1261, 1987;
  Abels--Brown, *Finiteness properties of solvable S-arithmetic groups: an
  example*, J. Pure Appl. Algebra 44 (1987)). As `n` varies these groups
  realise the finiteness gaps. The recorded index is type `F_{n-2}` but not
  `F_{n-1}`, with the `4 x 4` group finitely presented. That index was not
  re-read at the source on 2026-09-13, and nothing below depends on it. By
  definition `A_n(Z[1/p]) <= GL_n(Z[1/p])`. That is an S-arithmetic group in
  characteristic zero, so it is of type `F_∞` (Borel--Serre, *Cohomologie
  d'immeubles et de groupes S-arithmétiques*, Topology 15 (1976)). It has
  torsion (`-1` on the diagonal), so it is of type `F_∞` but not of type `F`.

Correction note (2026-09-13): the first version said "upper unitriangular"
for Abels' groups, gave the index as `F_{n-1}` but not `F_n`, credited the
characteristic-zero S-arithmetic finiteness to the wrong paper, and said
every family embeds in a group of type `F`. The review
`research/artifacts/zp-review-topology-2026-09-13-part1.md` §8a found these
defects. The id is unchanged; only the Abels host is weakened to type `F_∞`,
which is all Problem 1.1 needs.
