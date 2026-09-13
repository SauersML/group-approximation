---
rg: 2
id: transitive-wreath-towers-bounded-commutator-width
kind: claim
title: The derived subgroup of every iterated wreath product of transitive groups of degree at most m has commutator width at most 3(m! + m + 2)
distinct_from:
  full-cycle-wreath-towers-bounded-commutator-width: that needs a full cycle at every level and gets width max |T_i| by the twisted lemma; this needs nothing beyond transitivity and bounded degree, at the price of a larger constant, by a base lemma and a three-for-two absorption.
  iterated-simple-wreath-bounded-commutator-width: that treats simple levels through Nikolov--Segal and Lucchini--Menegazzo, so it depends on the classification; this is elementary and covers all transitive levels.
  nikolov-segal-uniform-commutator-width: that needs boundedly many generators; towers with many abelian levels need unboundedly many, and this bound does not care.
---

**ESTABLISHED (elementary).**

**Theorem.** Let `W = T_1 wr T_2 wr ... wr T_d` be an iterated permutational wreath product acting on a
rooted tree, with each `T_i <= Sym(m_i)` transitive and `m_i <= m`. Then every element of `[W, W]` is a
product of at most `3(m! + m + 2)` commutators of `W`, for every depth `d`.

**Base lemma.** Let `W = H wr T = H^m ⋊ T`, `beta in T`, and `g in H^m`. Suppose that on every cycle
`(i_1, beta(i_1), ..., beta^(L-1)(i_1))` of `beta`, fixed points included, the ordered product
`g_(beta^(L-1) i_1) ... g_(beta(i_1)) g_(i_1)` is a commutator in `H`. Then `(g; 1) = [(u; 1), (q; beta)]` for
some `u, q in H^m`.

**Three-for-two absorption.** Let `j_0 != i` be coordinates with `i = beta(j_0)` for some `beta in T`. If `z in H` is
a product of `3N` commutators of `H`, then `(z at j_0; 1)` is a product of `2N` commutators of `W`.

**Inheritance.** If every element of `[H, H]` is a product of `c_H` commutators, then every element of
`[W, W]` is a product of at most `|T| + (m - 1) + 2 ceil(c_H / 3)` commutators. The constant `3(m! + m + 2)`
is a fixed point of this recursion.

**Consequences.**
- **Relator width.** With `relator-width-over-towers-of-bounded-commutator-width`, every finitely presented
  group without finite quotients has depth-uniform relator width over all towers of bounded degree.
  This establishes `simple-nonsofic-relator-width-over-iterated-wreath-products`
  (`deep-wreath-relator-width-from-commutator-width`).
- **No classification needed.** This supersedes the classification-dependent route through
  `iterated-simple-wreath-bounded-commutator-width` for simple towers.

Derivation: `transitive-wreath-towers-bounded-commutator-width-proof`. Unreviewed.
Credit: elementary computation. No literature search was run. Bounds of this type for wreath
products may be known, and the constant is not optimized.
