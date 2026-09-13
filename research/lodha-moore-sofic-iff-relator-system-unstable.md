---
rg: 2
id: lodha-moore-sofic-iff-relator-system-unstable
kind: claim
title: The Lodha--Moore group is nonsofic exactly when almost-solutions of its relators in permutations almost commute
distinct_from:
  thompson-f-sofic-iff-relator-system-unstable: that is the same dictionary for Thompson's F, with abelianization Z^2; this is the Lodha--Moore group G_0, with abelianization Z^3, from its own character classification.
  lodha-moore-group-is-not-sofic: that is the nonsoficity statement; this proves it equivalent to permutation stability of the relators of G_0.
---

**ESTABLISHED (unreviewed).**  Let `G_0 = <a, b, c | S>` be a finite presentation
of the Lodha--Moore group (one exists by Lodha--Moore, arXiv:1308.4250), and let
`d` be the normalized Hamming distance.  The following are equivalent.

1. `G_0` is not sofic.
2. The relator system `S` is stable in permutations: every sequence of
   `delta_n`-solutions with `delta_n -> 0` is `o(1)`-close to exact solutions.
3. **Commutator form.** For every `epsilon > 0` there is `delta > 0` such that, for
   all `n` and all `A, B, C in Sym(n)` whose relator defects in `S` are below
   `delta`, the three commutator distances `d(AB, BA)`, `d(AC, CA)` and
   `d(BC, CB)` are below `epsilon`.
4. For every almost-homomorphism `phi_n : G_0 -> Sym(k_n)` and every ultrafilter,
   the fixed-point character `g -> lim |Fix phi_n(g)| / k_n` has no regular
   component.

**What it says.**
- Exact solutions of `S` in `Sym(n)` are exactly the commuting triples, because
  every finite quotient of `G_0` is abelian.
- So `G_0` is sofic exactly when some almost-solutions keep a fixed amount of
  noncommutation.

**Relation to `F`.**  `F <= G_0`, so nonsoficity of `F` gives item 1 through
`lodha-moore-not-sofic-from-thompson-f-not-sofic`.  No implication from item 3 to
the corresponding statement for `F` is claimed.

Derivation: `lodha-moore-sofic-iff-relator-system-unstable-proof`.
