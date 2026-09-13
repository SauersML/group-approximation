---
rg: 2
id: zaremsky-2-15-torsion-free-subgroups-of-v-embed-in-f
kind: claim
title: "Zaremsky Problem 2.15 resolved: does every torsion-free subgroup of V with no non-abelian free subgroups embed into F?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 15,
verbatim: "(Added 2/10/24) Does every torsion-free subgroup of `V` with no
non-abelian free subgroups embed into `F`? [Update 4/3/26: No, Corentin Bodart
points out the (torsion-free) Klein bottle group embeds in `V`, but cannot
embed in `F` since it is not bi-orderable. So perhaps the question should be
re-posed with “torsion-free” replaced by “bi-orderable”.]"

This claim is the question. It is established only through an answer route:

- **No**: `zaremsky-2-15-by-klein-bottle-group` requires
  `klein-bottle-group-embeds-in-v-but-not-in-f`.
- **Yes** would say that every such subgroup embeds into `F`. The Klein bottle
  group refutes it, so no yes-route is written.

Never write a `requires: []` route into this claim.

**Reading.** "Embed into `F`" means an injective homomorphism into Thompson's
group `F`. A counterexample is a subgroup of `V` that is torsion-free, has no
non-abelian free subgroup, and is not isomorphic to any subgroup of `F`.

**Status.** Answered negatively in the list's own note, from an observation of
Corentin Bodart. The reposed question, with "bi-orderable" in place of
"torsion-free", is the separate root
`zaremsky-2-15b-bi-orderable-subgroups-of-v-embed-in-f`.
