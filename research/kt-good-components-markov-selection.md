---
rg: 2
id: kt-good-components-markov-selection
kind: claim
title: Good expander components carry uniform multiplicativity, diverging size, injective labels and a vanishing edit budget
---

Let `S` be a sofic approximation of an infinite countable group `K`, let `T`
be a finite symmetric generating set, and let `D` be an expander decomposition
of `S` for `T`.  There is a predicate of good components whose complement has
total mass `o(|S_n|)` such that, for large `n` and uniformly over good
components `C`:

* for each fixed pair `g, h`, the completed component labels satisfy
  `d_H(c(gh), c(g) c(h)) < δ` for any prescribed `δ > 0`;
* `|C|` exceeds any prescribed bound;
* the completed labels of the elements of `T` are distinct;
* `C` is cluster good;
* the local edit budget, the ambient collisions of two distinct elements, the
  exits of a fixed element and the completed product errors are each at most
  `δ |C|`.

The proof applies Markov's inequality at a diagonal level to a countable
family of per-component error counts, each of negligible total.  This is step
G1f of the Kun--Thom Theorem 4.1 blueprint
(`research/artifacts/kt-theorem-4-1-blueprint-2026-09-12.md`).  It supplies
the `size_tendsTo`, `locallyMultiplicative` and `labelsInjective` fields of a
`ComponentFamily`.  It does not supply `expands`: completed labels expand only
at a scale, so the exact directed Cheeger bound needs the maximal sparse cut
pruning of lanes kt41-seq-decomp and kt41-g1-alt.

DERIVATION
kt-good-components-markov-selection-proof
