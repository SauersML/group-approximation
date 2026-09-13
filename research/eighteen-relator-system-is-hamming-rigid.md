---
rg: 2
id: eighteen-relator-system-is-hamming-rigid
kind: claim
title: Almost-solutions of the eighteen Leavitt-Thompson relators in symmetric groups are almost trivial, uniformly in the degree
distinct_from:
  explicit-eighteen-relator-nonsofic-group: that is nonsoficity of the presented group; this is the equivalent finitary statement about almost-solutions in finite symmetric groups, with one epsilon-delta uniform over all degrees.
  leavitt-hyperlinearity-eighteen-relator-unitary-test: that is the unitary, Hilbert--Schmidt analogue, whose answer is unknown; this is the permutation, Hamming statement, which is proved.
---

**ESTABLISHED (2026-09-12, unreviewed)** through `eighteen-relator-system-is-hamming-rigid-proof`.

Let `r_1..r_18` be the relators of `thompson-steinberg-presentation-of-leavitt-unit-group`, words
in `a, b, c, x`. Let `d_H(s,t) = |{i : s(i) != t(i)}| / n` on `Sym(n)`.

**Claim.** For every `epsilon > 0` there is `delta > 0` with the following property. For every
`n` and all `s_a, s_b, s_c, s_x in Sym(n)`, if
`d_H(r_j(s_a,s_b,s_c,s_x), id) <= delta` for `j = 1..18`, then
`d_H(s_g, id) <= epsilon` for `g = a, b, c, x`.

The system itself is not trivial. It has an exact solution with `x != 1` in `L_(F_2)(1,2)^x`
(the stated images), and its only exact solution in a sofic group is `a = b = c = x = 1`.

So eighteen equations in four permutations are a *finite nonsoficity test*. No degree admits an
almost-solution that is far from trivial. By contrast, any almost-solution close to the trivial
one only needs its generators to be almost trivial, which costs nothing.

## Attempts

- **Explicit delta.** The proof is by compactness and gives no explicit `delta(epsilon)`. An
  explicit bound would need a quantitative form of every step: the Kazhdan constants of the
  expanding approximation in the nonsoficity proof, a quantitative non-LEF witness, and a
  Hamming form of the Tietze comparison. Not attempted.
