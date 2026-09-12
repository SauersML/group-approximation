---
rg: 2
id: finite-bi-index-decidable-membership-proof
kind: route
title: Dovetail the finitely many double-coset searches
target: finite-bi-index-subgroups-have-decidable-membership
requires: []
---

Fix words `s_1,...,s_k` generating `S`, words `g_1 = 1, g_2, ..., g_m` with

```text
Gamma = S g_1 S  ⊔  S g_2 S  ⊔  ...  ⊔  S g_m S,
```

and an algorithm for the word problem of `Gamma`.

Given a word `w`, run `m` searches in parallel. Search `i` enumerates pairs of
words `u, v` in `s_1^{±1},...,s_k^{±1}` and uses the word-problem algorithm to
test whether `u g_i v = w`. Search `i` succeeds exactly when `w in S g_i S`.
The double cosets partition `Gamma`, so exactly one search succeeds and the
dovetailed procedure halts with its index. Answer "yes" iff that index is `1`.

The procedure uses finitely many fixed words and the word-problem algorithm, so
it exists. It is not uniform in the data: finiteness of the double coset space
is exactly what guarantees that the parallel search halts. `∎`
