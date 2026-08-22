---
rg: 2
id: leavitt-three-gate-amalgam-injectivity-proof
kind: route
title: Identify the paired quotient as an amalgam over the twice-embedded exact corner group
target: leavitt-three-gate-candidate-is-injective
requires:
  - leavitt-corner-subgroup-is-v4-v4-f2
  - three-gate-tietze-map-is-nielsen-embedded
---

Let `C=G_0*G_1` and let `Q` be the abstract corner group.  The first
prerequisite embeds `Q` in `C`.  Let `P` be the quotient of `Q*<z>` by the
two paired relators; the second prerequisite embeds `Q` in `P`.

The full paired quotient is the pushout `C *_Q P`.  Since both edge maps are
injective, the normal-form theorem for free products with amalgamation
injects each vertex group, in particular `C`, into the pushout.  This is the
claimed coefficient injection.
