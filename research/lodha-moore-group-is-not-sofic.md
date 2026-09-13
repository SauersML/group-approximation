---
rg: 2
id: lodha-moore-group-is-not-sofic
kind: claim
title: The Lodha--Moore group is not sofic
distinct_from:
  lodha-moore-group-is-bi-orderable-and-not-lea: that settles bi-orderability and failure of LEA for the Lodha--Moore group; this asks for failure of the weaker property soficity.
  thompson-f-is-not-sofic: that is nonsoficity of Thompson's F; this is nonsoficity of the Lodha--Moore group G_0, and this node does not check whether F embeds in G_0.
---

**Statement (OPEN).**  The Lodha--Moore group `G_0`, the finitely presented
subgroup of Monod's group of piecewise projective homeomorphisms of `R`
(Lodha--Moore, arXiv:1308.4250), is not sofic.

**Why it matters.**  `G_0` is bi-orderable
(`lodha-moore-group-is-bi-orderable-and-not-lea`).  So this claim gives a
left-orderable nonsofic group through
`left-orderable-non-sofic-via-lodha-moore-group`, with no Kazhdan subgroup
involved.

**What is already known about `G_0`** (from the established node and its proof
route):

- finitely presented, torsion-free and nonamenable;
- bi-orderable;
- every proper quotient is abelian (Burillo--Lodha--Reeves), so `G_0` is not
  residually amenable, not LEA and not LEF.

Failure of LEA already rules out the elementary certificate of soficity:
local embeddings into amenable groups.

## Attempts

**Not attempted: an F-type dictionary.**
`thompson-f-sofic-iff-relator-system-unstable` shows that `F` is nonsofic
exactly when almost-solutions of its relators correct through its
abelianization.  That proof uses two facts: every finite quotient of `F` is
abelian, and the characters of `F` are classified (`thompson-f-character-simplex`).
`G_0` has the first property, since all its proper quotients are abelian.  A
classification of the characters of `G_0` is not recorded in this graph, and
the literature was not checked for one.  With it, the same argument would
reduce this claim to permutation stability of the relators of `G_0`.

**Not checked: embedding of `F` in `G_0`.**  If `F` embeds in `G_0`, then
`thompson-f-is-not-sofic` implies this claim, because soficity passes to
subgroups.  This node does not verify such an embedding.
