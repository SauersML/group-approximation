---
rg: 2
id: fp-simple-group-with-at-least-exponential-dehn-function
kind: claim
title: Some finitely presented simple group has at least exponential Dehn function
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's embedding theorem for finitely presented self-similar groups, with no Dehn-function content; this is his earlier lower bound on the Dehn function of one specific Rover--Nekrashevych commutator subgroup, obtained through a quasi-retraction rather than an embedding.
  fp-simple-dehn-functions-realize-every-recursive-lower-bound: that asks for every recursive lower bound; this is the single case f(n) = 2^n, the largest one known.
---

**ESTABLISHED (literature import).** There is a finitely presented simple group
`S` with `2^n ≼ delta_S`.

> **Theorem 3.2** (M. C. B. Zaremsky, *Finitely presented simple groups with at
> least exponential Dehn function*, arXiv:2305.15176v2, 11 July 2024, to appear in
> Michigan Math. J.). There exist finitely presented simple groups with at least
> exponential Dehn function.

The examples are `[V_{n+2}(BS(1,n)), V_{n+2}(BS(1,n))]`. From the introduction
(p. 2): a self-similar representation of `BS(1,n)` on the `(n+2)`-ary tree "is
calibrated to have a variety of properties ... which ensure that, among other
things, the Röver–Nekrashevych group `V_{n+2}(BS(1,n))` has `BS(1,n)` as a
quasi-retract, and its commutator subgroup has finite index and is simple".
`BS(1,n)` has exponential Dehn function [Ger92], quasi-retracts have smaller Dehn
functions (Citation 1.2), and a finite-index subgroup has the same Dehn function up
to `≃`.

**Scope.** Only a lower bound is claimed. The paper does not approach an upper
bound; it suspects the Dehn function of `V_d(G)` is bounded by a combination of
those of `V_d({1})` and `G`.

DERIVATION
fp-simple-exponential-dehn-zaremsky-citation
