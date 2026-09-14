---
rg: 2
id: thompson-v-conjugacy-finite-obstruction-proof
kind: route
title: Conjugation preserves order, and a left comb of cones gives V elements of every order
target: thompson-v-embeds-in-no-conjugacy-finite-group
requires:
  - thompson-v-finitely-presented-infinite-simple
  - simple-envelope-forces-solvable-word-problem
---

**1. Orders are conjugacy invariants.** For `x, g` in a group and `n >= 1`,
`(g x g^-1)^n = g x^n g^-1`, so `x^n = 1` exactly when `(g x g^-1)^n = 1`.
So conjugate elements have the same order, finite or infinite. If a group has
conjugacy classes `c_1, ..., c_k`, every element has the order of the
representative of its class, and at most `k` orders occur.

**2. Elements of every order in V.** Let `C = {0,1}^N` and `n >= 2`. Put
`w_i = 0^(i-1) 1` for `1 <= i <= n-1` and `w_n = 0^(n-1)`.
- The words `w_1, ..., w_n` form a complete prefix code: every infinite word
  either begins with `0^(i-1) 1` for a unique `i <= n-1`, or begins with
  `0^(n-1)`, and no `w_i` is a prefix of another. So the cones `[w_i]`
  partition `C`.
- Define `g(w_i z) = w_(i+1) z` for `1 <= i <= n-1` and `g(w_n z) = w_1 z`.
  It replaces the prefixes of one complete prefix code by those of a complete
  prefix code of the same size, so `g` lies in `V`.
- `g^j` sends `[w_1]` to `[w_(1+j)]` for `0 < j < n`, which is disjoint from
  `[w_1]`, so `g^j != 1`. And `g^n(w_i z) = w_i z` for every `i`, so `g^n = 1`.
  Thus `g` has order `n`. The identity has order `1`.

**3. V is a decidable input.** `V` is finitely presented, infinite and simple
(`thompson-v-finitely-presented-infinite-simple`), so it is finitely generated,
and it has solvable word problem by `simple-envelope-forces-solvable-word-problem`
applied to `V <= V`.

**4. Conclusion.** Suppose `V <= T`. By step 2, `T` has elements of every
finite order `n >= 1`, so infinitely many distinct element orders. By step 1,
`T` has infinitely many conjugacy classes. So no group with finitely many
conjugacy classes contains `V`. Since `V` is finitely generated with solvable
word problem (step 3), the universal statement
`every-wp-group-embeds-in-fp-conjugacy-finite-group` fails at `G = V`.

**5. The general fiber-product data.** If `N <| T` has finitely many
`T`-conjugacy classes, step 1 applied to `T`-conjugation shows that `N` has
finitely many element orders. This constrains only the elements of the input
lying in `N`, so `universal-fiber-product-data-for-word-problem-groups` is not
refuted.
