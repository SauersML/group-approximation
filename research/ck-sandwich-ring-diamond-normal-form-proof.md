---
rg: 2
id: ck-sandwich-ring-diamond-normal-form-proof
kind: route
title: Bergman's Diamond Lemma with the group-multiplication rules and the single rule p g q -> p q - 1, which has no ambiguities with itself
target: ck-sandwich-ring-diamond-normal-form
requires: []
---

**Import.** G. M. Bergman, *The diamond lemma for ring theory*, Adv. Math. 29
(1978), 178--218, Theorem 1.2. Let `k` be a commutative ring, `X` a set, `S` a
reduction system of pairs `(W_s, f_s)` with `W_s` a word and `f_s in k<X>`.
Suppose `<X>` carries a semigroup partial order with the descending chain
condition, compatible with `S` (every `f_s` is a combination of words `< W_s`).
Then all ambiguities of `S` are resolvable relative to `<=` iff the
`S`-irreducible words form a `k`-basis of `k<X> / (W_s - f_s)`.

**Setup.** Take `k = Z` and `X = (T \ {1}) ⊔ {p, q}`. The reduction system has
two kinds of rules.
- **(G)** For `t, t' in T \ {1}`: `t t' -> (tt')` if `tt' != 1`, and `t t' -> 1`
  otherwise.
- **(P)** `p g q -> p q - 1`.

The (G) relations present `Z[T]` inside `Z<X>`. So `Z<X>/(G, P)` is
`Z[T] * Z<p,q>` modulo `pgq - pq + 1`, and `pgq - pq + 1 = p(1-g)q - 1` up to
sign. That quotient is `U`.

**Order.** Order words by length. This is a semigroup partial order,
`|A| < |B|` implies `|CAD| < |CBD|`, and it has DCC. It is compatible with the
rules: `|t t'| = 2 > 1 >= |(tt')|`, and `|pgq| = 3 > |pq| = 2 > |1| = 0`.

**Ambiguities.**
- **(G)/(G) overlaps** `t t' t''` resolve by associativity of `T`. Both sides
  reduce to the single letter `(tt't'')`, or to `1`. If an intermediate product
  is trivial, the one-letter remainder is reached in one more step.
- **(P)/(P).** The leading word `pgq` begins with `p` and ends with `q`, so a
  proper suffix of it (`q` or `gq`) is never a prefix of it (`p` or `pg`). There
  are no overlap ambiguities. There is no inclusion ambiguity, since both words
  have length 3.
- **(G)/(P).** A (G) leading word consists of two letters of `T`. The only `T`
  letter of `pgq` is `g`, flanked by `p` and `q`. So no (G) word overlaps `pgq`
  or is contained in it.

All ambiguities resolve. The irreducible words are those with no two adjacent
`T` letters and no segment `p g q`. These are exactly the words of item 1, with
the convention `t_i = 1` for an absent interior letter. So item 1 holds, and
each `t in T` is an irreducible word, which gives `T -> U` injective.

**Word problem (item 2).** Given ring words, expand them into Z-combinations
of words in `X`. Apply (G) and (P) until no rule applies. Each step strictly
lowers the length-multiset, so this terminates. To apply (G) one must compute
`tt'` in `T` and decide `tt' = 1`. To detect (P) one must decide `t_i = g`. Both
use the word problem of `T`. By the basis theorem the resulting irreducible form
is unique, so two elements are equal iff their normal forms agree. The converse
holds because `T` embeds in `U` (item 1).

**Matrices (item 3).** An element of a finitely generated subgroup of
`GL_n(U)` is a product of the given generator matrices and their inverses, each
with entries given as ring words. Multiply the matrices entrywise, reduce each
entry to normal form, and compare with the identity matrix. By item 2 this is
decidable. ∎
