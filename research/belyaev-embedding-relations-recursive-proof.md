---
rg: 2
id: belyaev-embedding-relations-recursive-proof
kind: route
title: The enumeration, equality set, and counting function are computable from a solvable word problem, so every Belyaev relation set is recursive
target: belyaev-embedding-relations-are-recursive-for-decidable-input
requires:
  - belyaev-associative-higman-theorem
---

Fix a finite generating set `g_1, …, g_k` of `A`. "Solvable word problem" means
it is decidable which noncommutative `K`-polynomials in `g_1, …, g_k` vanish in
`A`; equivalently, equality of two such polynomials in `A` is decidable.

**1. Computable enumeration.** The set `P` of formal noncommutative
`K`-polynomials in `g_1, …, g_k` is computably enumerable: words in the `g_i`
are computably enumerable, and `K` is decidable, so finite `K`-combinations of
words can be listed `p_1, p_2, …`. Interleave this list with itself
(`p_1, p_1, p_2, p_1, p_2, p_3, …`) and set `a_i` to be the `i`-th term. Then
`i ↦ a_i` is computable, every element of `A` is represented (each `p_n`
represents an element and appears), and every element is represented infinitely
often, so in particular at least twice, as Belyaev's proof requires.

**2. `Y` is decidable.** Under Lemma 3 the embedding `A ↪ B` is faithful and
`a_i` corresponds to `a b^i c`, so `a b^i c = a b^j c` in `B` iff `a_i = a_j` in
`A`. The latter is `a_i - a_j` vanishing in `A`, decidable by the solvable word
problem. Hence `Y = {⟨i,j⟩ : a_i = a_j}` is decidable.

**3. `f` is computable.** For each `i, j` the polynomial `a_i + a_j` represents
an element of `A`, so by step 1 there is an index `m` with `a_m = a_i + a_j`.
The predicate "`a_m = a_i + a_j` in `A`" is decidable, so `f(i,j) := ` least
such `m` is computable by unbounded search, which is guaranteed to halt.

**4. Recursive relation sets.** The defining relations of the special algebra
`S` are
`{x y^i z + x y^j z = x y^{f(i,j)} z : i ≠ j} ∪ {x y^i z = x y^j z : ⟨i,j⟩ ∈ Y}`.
Given a candidate relation one reads off `i, j` from the exponent blocks and
checks it against computable `f` and decidable `Y`; so this set is recursive.
Lemma 2 builds `S_1` using, besides `f` and `Y`, only the pairing functions
`n_i(j)` and `s(i,j)` read off the line-intersection diagram; these are
primitive recursive and one-to-one. So the word-equality set `Σ` of `S_1` is
recursive, and the semigroup `G` presented by `Σ` has a recursive set of
defining relations. The counting semigroup `H` is presented by
`{ρ g^i τ = ρ g^{g(i,j)} τ}` for a recursive `g` obtained the same way as `f`
(search for the index witnessing an equality guaranteed to hold), so its
relation set is recursive as well.

**On `K`.** Steps 1–4 use only that `K` is decidable. For `K = F_p` or `Q`, and
for any field finitely generated over its prime field with decidable equality,
the hypotheses of `belyaev-associative-higman-theorem` on `K` also hold, so the
construction applies. ∎
