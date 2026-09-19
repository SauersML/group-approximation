---
rg: 2
id: wreath-base-conjugacy-classes-are-finite-multisets
kind: claim
title: In a permutational wreath product the conjugacy classes of the base are the finite multisets of base classes, so there are infinitely many of them
invalidates: [fiber-product-data-via-permutational-wreath]
distinct_from:
  fiber-product-conjugation-action-lemma: that computes orbits and stabilizers of the fiber product action on an arbitrary normal subgroup; this computes the conjugacy classes of one specific normal subgroup in one specific family of groups, and its content is that the count is infinite.
  every-wp-group-embeds-in-fp-conjugacy-finite-group: that asks for a finitely presented overgroup with finitely many conjugacy classes; this proves one natural family of candidates never has finitely many, and so is an obstruction to the obvious attack on it rather than a version of it.
  simple-core-bi-index-counts-coset-action-pair-orbits: that identifies pair orbits of a coset action with a double coset set; this identifies conjugacy classes of a wreath base with finite multisets, and its point is a lower bound on their number.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Let `S` be a set, `B` a group, and

    T  =  B wr_S Sym_fin(S)  =  B^{(S)} : Sym_fin(S)

the permutational wreath product, with base `N = B^{(S)}` the finitely
supported functions `S -> B`.  Then two elements `x, y` of `N` are
`T`-conjugate exactly when the finite multisets

    { [x(s)]_B : s in supp(x) }   and   { [y(s)]_B : s in supp(y) }

of nontrivial `B`-conjugacy classes agree.

Consequently, if `S` is infinite and `B != 1` then `N` has **infinitely
many** `T`-conjugacy classes.

## Proof

For `(b, sigma) in T` and `x in N`,

    ((b,sigma) . x . (b,sigma)^{-1}) (s)  =  b(s) . x(sigma^{-1} s) . b(s)^{-1} .

So conjugation permutes the coordinates by `sigma` and conjugates each value
inside `B` by `b(s)`.  The multiset of `B`-classes of the nontrivial values
is therefore invariant.  Conversely, given `x, y` with equal multisets,
choose a bijection between their supports matching classes -- possible
because the multisets agree and both supports are finite -- extend it to a
finitely supported permutation `sigma`, and choose `b(s)` realizing the
conjugation in `B` at each point of `supp(y)`, arbitrary elsewhere.  Then
`(b,sigma)` carries `x` to `y`.

For the count: pick `c != 1` in `B`.  Since `S` is infinite, for every
`n >= 0` there is an `x_n in N` whose nontrivial values are `n` copies of
`c`.  Their invariants are the multisets `{[c], ..., [c]}` of size `n`,
pairwise distinct.  `∎`

## Why the graph carries it

It kills the first construction anyone reaches for when trying to satisfy
clause 6 of `universal-fiber-product-data-for-word-problem-groups`.  A
wreath product looks ideal: the top group is finitary and highly transitive,
so positional information is destroyed, and the base is as large and as
flexible as one likes.  The proof above says the destruction is only
positional -- the **labels** survive, and unbounded support size turns them
into an unbounded invariant.  The count fails for the crudest possible
reason, which is worth recording because the failure is invisible until the
invariant is written down.

The same computation says what a repair would have to do: it must bound the
support size, which finitely supported functions do not admit, or make the
top group act on `B^{(S)}` by something other than coordinate permutation.
Houghton-style enlargements of `Sym_fin(S)` change the top group and not the
invariant, so they do not help.
