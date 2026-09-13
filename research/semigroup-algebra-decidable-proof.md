---
rg: 2
id: semigroup-algebra-decidable-proof
kind: route
title: Sort the words of a polynomial into decidable semigroup-equality classes and test coefficient sums
target: semigroup-algebra-of-decidable-semigroup-is-decidable
requires: []
---

Elements of `K[H]` are represented by finite formal `K`-combinations
`p = Σ_{t=1}^{r} c_t w_t`, where each `w_t` is a word in the generators of `H`
and `c_t ∈ K`. As an element of `K[H]`, `p` equals `0` iff, after grouping the
words into classes under equality in `H` and summing coefficients within each
class, every class sum is `0` in `K`.

**Decision procedure.** Given `p`:

1. The words `w_1, …, w_r` are finite in number. For each pair `t, t'` decide
   `w_t = w_{t'}` in `H`; this is the word problem of `H`, which is solvable.
   This partitions `{1, …, r}` into equality classes.
2. For each class `C` compute `Σ_{t ∈ C} c_t ∈ K`; the field operations are
   computable because `K` is decidable.
3. Output "`p = 0`" iff every class sum is `0`, which is decidable because
   equality in `K` is decidable.

Correctness: `K[H]` is free as a `K`-module on the elements of `H` (a basis
indexed by the distinct semigroup elements), so `p = 0` in `K[H]` exactly when
the coefficient of each distinct semigroup element is `0`, i.e. each class sum
vanishes. For `K[H^1]` the adjoined identity is one more basis element, handled
as its own class. ∎

Independence of generating set: two finite generating sets give a computable
translation of words, so solvability of the word problem, and hence of this
procedure, does not depend on the chosen generators.
