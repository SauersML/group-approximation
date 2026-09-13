---
rg: 2
id: standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups
kind: claim
title: "Every classical group of type F_n but not F_{n+1} embeds in a group of type F"
---

Each of the standard families of groups that are of type `F_n` but not of
type `F_{n+1}` is, by its very construction, a subgroup of a group of type
`F` (finite `K(pi,1)`), hence embeds in a group of type `F_infinity`. So none
of them is a counterexample to Zaremsky Problem 1.1, and the negative answer
`some-type-fn-group-embeds-in-no-type-fn-plus-1-group`, if true, needs a group
outside this reservoir.

- **Bieri--Stallings groups.** `SB_n = ker(F^{(1)} x ... x F^{(n)} -> Z)`,
  the kernel of the map from a direct product of `n` nonabelian free groups
  to `Z` sending every free generator to `1` (Bieri, *Homological dimension
  of discrete groups*, QMC Notes 1976; Stallings 1963 for `n = 3`). `SB_n` is
  of type `F_{n-1}` but not `FP_n`, hence not `F_n`. By definition
  `SB_n <= F^{(1)} x ... x F^{(n)}`, a direct product of free groups, which is
  of type `F` (its `K(pi,1)` is a product of finite graphs).

- **Bestvina--Brady groups.** For a finite flag complex `L`,
  `BB_L = ker(A_L -> Z)`, the kernel of the RAAG `A_L` mapping each standard
  generator to `1` (Bestvina--Brady, *Morse theory and finiteness properties
  of groups*, Invent. Math. 129 (1997)). `BB_L` is of type `F_n` iff `L` is
  `(n-1)`-connected and can be of type `FP_{n+1}` but not `F_{n+1}` (their FP
  vs. F separation). By definition `BB_L <= A_L`, and every right-angled Artin
  group is of type `F` (the Salvetti complex is a finite `K(pi,1)`).

- **Abels' groups.** For `n >= 2` Abels' group `A_n(Z[1/p])` of upper
  unitriangular matrices with `1`s in the corners is of type `F_{n-1}` but not
  `F_n` (Abels, LNM 1261, 1987; Abels--Brown, *Finiteness properties of
  solvable S-arithmetic groups*, J. Pure Appl. Algebra 44 (1987)). It is by
  definition a subgroup of `GL_n(Z[1/p])`, an S-arithmetic group, which is of
  type `F_infinity` (S-arithmetic groups in characteristic zero are of type
  `F_infinity`; Borel--Serre for arithmetic groups, and the S-arithmetic case
  e.g. via Bux--Köhl--Witzel and reduction theory).

Thus the classical `F_n`-not-`F_{n+1}` examples all embed in type-`F`
(hence type-`F_infinity`) groups; they witness the *sharpness* of Problem 1.1
rather than answering it.
