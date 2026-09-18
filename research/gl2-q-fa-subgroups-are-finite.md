---
rg: 2
id: gl2-q-fa-subgroups-are-finite
kind: claim
title: Every subgroup of GL_2(Q) or PGL_2(Q) with Serre's property FA is finite, so fixed-point obstructions exclude no host for the n = 2 case
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the embedding problem; this says which host obstructions cannot help for n = 2 (the cube-complex fixed-point argument of survey Remark 4.12 that excludes V and VA for n >= 3).
  lifts-add-no-unipotent-divisibility: that rules out lifts as hosts; this rules out fixed-point arguments as obstructions for n = 2.
---

**ESTABLISHED** through `gl2-q-fa-subgroups-are-finite-proof` (elementary; not
independently reviewed; no novelty claimed).

## Statement

Let `H` be a subgroup of `GL_2(Q)` or of `PGL_2(Q)` with Serre's property FA
(every action on a tree without inversions has a fixed vertex). Then `H` is
finite. The same holds for subgroups of `SL_2(Q)` and `PSL_2(Q)`.

Property FW (every action on a CAT(0) cube complex has a bounded orbit)
implies FA, since a tree is a one-dimensional CAT(0) cube complex. So every
FW subgroup of these groups is finite as well.

## Consequence for hosts

Survey arXiv:2306.16356v3, Remark 4.12, excludes `SL_n(Z)`, `n >= 3`, from
`VA` because "any action of any finite index subgroup of `SL_n(Z)` (`n >= 3`) on
any CAT(0) cube complex must fix a point" (Cornulier). An argument of this
shape needs an infinite subgroup of the input all of whose finite-index
subgroups have FW. By the statement, no subgroup of `GL_2(Q)`, `SL_2(Q)`,
`PGL_2(Q)` or `PSL_2(Q)` qualifies. So for the `n = 2` claims
(`gl2-q-embeds-in-fp-simple-group`, `sl2-q-embeds-in-fp-simple-group`,
`psl2-q-embeds-in-fp-simple-group`), fixed-point arguments on trees or cube
complexes cannot exclude any host. That includes hosts acting on CAT(0) cube
complexes with small stabilizers, such as `V`, `nV` or twisted Brin--Thompson
groups. For `n = 2` an exclusion has to use another invariant: divisibility
(O1 of `gl-n-q-embeds-in-fp-simple-group`), distortion (O4 there), or analytic
rigidity of a natural action. For `n >= 3` the fixed-point route stays
available through `SL_3(Z) <= GL_3(Q)`.
