---
rg: 2
id: lodha-moore-group-is-not-sofic
kind: claim
title: The Lodha--Moore group is not sofic
distinct_from:
  lodha-moore-group-is-bi-orderable-and-not-lea: that settles bi-orderability and failure of LEA for the Lodha--Moore group; this asks for failure of the weaker property soficity.
  thompson-f-is-not-sofic: that is nonsoficity of Thompson's F; this is nonsoficity of the Lodha--Moore group G_0, which contains F (thompson-f-is-a-subgroup-of-lodha-moore-group), so that claim implies this one and the converse is not known.
  lodha-moore-sofic-iff-relator-system-unstable: that proves this claim equivalent to permutation stability of the relators of G_0; this is the nonsoficity statement itself.
---

**Statement (OPEN).**  The Lodha--Moore group `G_0`, the finitely presented
subgroup of Monod's group of piecewise projective homeomorphisms of `R`
(Lodha--Moore, arXiv:1308.4250), is not sofic.

**Why it matters.**  `G_0` is bi-orderable
(`lodha-moore-group-is-bi-orderable-and-not-lea`).  So this claim gives a
left-orderable nonsofic group through
`left-orderable-non-sofic-via-lodha-moore-group`, with no Kazhdan subgroup
involved.

**What is known about `G_0`:**

- finitely presented, torsion-free and nonamenable;
- bi-orderable;
- every proper quotient is abelian (Burillo--Lodha--Reeves), so `G_0` is not
  residually amenable, not LEA and not LEF;
- `G_0'` is simple, consists of compactly supported elements, and
  `G_0/G_0' ≅ Z^3` on the basis `a, b, c`
  (`lodha-moore-commutator-simple-abelianization-z3`);
- `G_0` contains Thompson's `F` as `<a, b>`
  (`thompson-f-is-a-subgroup-of-lodha-moore-group`).

Failure of LEA already rules out the elementary certificate of soficity:
local embeddings into amenable groups.

## Attempts

**Settled 2026-09-13: the F-type dictionary.**  The characters of `G_0` are
classified (`lodha-moore-group-character-simplex`): regular plus characters of
`Z^3`.  The proof transports the Dudko--Medynets dyadic compressibility lemma to
the action of `G_0'` on `R`.  As for `F`, this claim is equivalent to permutation
stability of the relators of `G_0`, that is, to almost-solutions in `Sym(n)` almost
commuting uniformly in `n` (`lodha-moore-sofic-iff-relator-system-unstable`).
Both nodes are ESTABLISHED and not independently reviewed.

**Settled 2026-09-13: `F` embeds in `G_0`.**  So `thompson-f-is-not-sofic`
implies this claim (`lodha-moore-not-sofic-from-thompson-f-not-sofic`).  A sofic
`G_0` would make `F` sofic.  Nothing here shows that nonsoficity of `G_0` forces
nonsoficity of `F`.

**Remaining gap.**  Permutation stability of the relators of `G_0` in the
commutator form, or nonsoficity of `F`.  Both remain open.
