---
rg: 2
id: weak-kervaire-transfers-only-at-unimodular-degree
kind: claim
title: The weak Kervaire conjecture transfers only at unimodular degree
invalidates: [kl-via-weak-conjecture-import]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Two statements travel under one name.

*Weak (Kervaire's weight form).*  If `G != 1` then
`(G * <t>)/<<w>> != 1`.

*Nonsingular (this repository's form).*  If `deg_t(w) = m != 0` then
`G -> (G * <t>)/<<w>>` is injective — that is
`kervaire-laudenbach-nonsingular-conjecture`.

For the weak conjecture the degrees `m = 0` and `|m| > 1` are automatic:
killing `G` and sending `t` to a generator gives a surjection onto `Z` and
onto `C_|m|` respectively, so the quotient is nontrivial for free.  All the
weak conjecture's content sits at `m = ±1`, and Klyachko's equivalence is
with **unimodular** coefficient injectivity.

Hence a proof of the weak conjecture does not, on its own, deliver
injectivity at `|m| > 1`.

## Why this matters here and where it does not

It matters for *imports*: a claimed proof of the weight-one statement is not
a proof of what `kervaire-laudenbach-holds-for-hyperlinear` supplies, so it
cannot be dropped into this graph as an establishment of the nonsingular
conjecture.  Recorded dead: `kl-via-weak-conjecture-import`.

It does **not** matter for the falsification lane.  A counterexample at any
nonzero degree suffices for `kl-violation-refutes-hyperlinearity-route`,
because the hyperlinear theorem being contradicted is itself the strong form.
The asymmetry is worth keeping straight: the scope caution binds proofs
coming in, not counterexamples going out.

The exponent-sum computation above is the whole content of the claim and is
elementary; the Klyachko reference is recorded for the unimodular equivalence
only and was not read from source this session.
