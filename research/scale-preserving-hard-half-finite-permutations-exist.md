---
rg: 2
id: scale-preserving-hard-half-finite-permutations-exist
kind: claim
title: For every recursive bound there is a half-finite scale-preserving involution with sub-double displacement whose evaluation beats that bound
distinct_from:
  hard-half-finite-permutations-have-fp-shift-envelopes: that also demands finite presentation of the envelope with E_2; this supplies only the generator, half-finite with displacement below 4x and hard, and makes no finite-presentation claim, so it isolates finite presentation as the entire remaining content of that target.
  fp-bounded-displacement-e2-envelopes-are-eventually-periodic: that shows bounded-displacement generators of a finitely presented envelope are eventually periodic hence easy; this exhibits a hard generator, so its displacement is necessarily unbounded, and it is realized scale-preservingly with sup_x gamma(x)/x <= 2.
  half-finite-shift-envelope-wp-computes-generators: that lower-bounds the envelope word problem by the cost of evaluating the generators; this constructs generators whose evaluation is above a prescribed bound, the input that lower bound consumes.
---

**ESTABLISHED** by `scale-preserving-hard-half-finite-permutations-exist-proof`.

For every recursive non-decreasing `R : N -> N` there is `gamma in Sym(N)` with:

1. `gamma` is an involution fixing every even number, so it has half-finite
   support;
2. `gamma` is **scale-preserving**: `gamma(B_j) = B_j` for every dyadic block
   `B_j = { x : 2^j <= x < 2^(j+1) }`, hence `x/2 < gamma(x) < 2x` for all
   `x >= 2`, in particular `gamma(x) <= 4x`;
3. the evaluation map `n -> gamma(n)` (with `n` in unary) is **not** in `F(R)`,
   the class `{ f : f computable in time C*R(C*n) + C*n + C for some C }` of
   `uniform-wp-bound-excludes-bh-universal-targets` (UWB1), read for maps
   `N -> N`.

So clauses 1 and 2 of `hard-half-finite-permutations-have-fp-shift-envelopes`
are met by a single generator, with room to spare on displacement: the whole
difficulty of that target lies in its clause 3, finite presentation of
`< gamma, sl, flip, (1 2) >`. By
`half-finite-generators-with-e2-are-strongly-shift-similar` this envelope is
already finitely generated and strongly shift-similar for any half-finite
`gamma`, so finite presentation is the sole obstacle, not displacement growth
and not the reach of the hardness.

The displacement here is unbounded — `sup_x |gamma(x) - x| = infinity` — as
`fp-bounded-displacement-e2-envelopes-are-eventually-periodic` requires of any
hard witness, yet it never exceeds the trivial scale bound `gamma(x) < 2x`. So
a witness for the open target need not push displacement toward the `4x`
ceiling; it must instead tie the blocks together by a finite rule (clause 1 of
`fp-alt-fin-envelopes-are-unique-solutions-of-their-relators` forces `gamma` to
be the unique solution of the presentation), and that finite rule must still
evaluate above `R`. No novelty is claimed; the construction is a diagonalization
inside dyadic blocks.
