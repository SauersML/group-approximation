---
rg: 2
id: two-level-kl-extreme-block-screen-proof
kind: route
title: Apply the extreme-height block theorem over P and read the coset level of a finite-order middle coefficient
target: two-level-kl-violations-need-torsion-in-an-extreme-block
requires: [kl-holds-when-extreme-height-blocks-have-infinite-order]
artifacts:
  - research/artifacts/hl-kl-two-level-words-2026-09-14.md
---

Notation of the target.

**Item 2.** Apply `kl-holds-when-extreme-height-blocks-have-infinite-order` with
coefficient group `P`. Its item 2 turns "every constrained block has infinite
order" into "no constrained block is an odd inverse palindrome around a
finite-order coefficient". So `P -> P_w` is injective. For `G >= P`,
`G * <t> = G *_P (P * <t>)`. Imposing `w = 1` in the second factor gives
`G_w = G *_P P_w`, and `G` embeds by the normal form theorem for amalgamated
free products. The last sentence of item 2 is the corollary of that theorem.

**Item 1.** This is the contrapositive of item 2. A finite-order element of `P`
does not lie in the torsion-free subgroup `H`, so it lies in some `a^j H` with
`j != 0 mod n`.

For `n = 2`, let `ha in aH` have finite order. Then `(ha)^2 = h a h a^(-1) a^2
= h sigma(h) a^2 in H`. It has finite order, so it is trivial, and `ha` is an
involution.

**Item 3.** Read the level of a letter as in the target of
`kl-pivot-letter-words-inject-over-torsion-free-by-finite`: substitute `t -> 1`
and reduce the prefix modulo `H`. The coefficient between two letters at levels
`lambda` and `mu` lies in `lambda^(-1) mu` mod `H`. For letters at the same level
it lies in `H`: it is trivial, or has infinite order since `H` is torsion-free.
So every finite-order coefficient changes level.

In a normal form over `P`, the coefficient between consecutive powers of `t`
is the product of the coefficients of `W` and the powers of `a` between them.
Its coset is determined by the levels of the letters it separates, so the
statement is independent of the chosen conjugate.
