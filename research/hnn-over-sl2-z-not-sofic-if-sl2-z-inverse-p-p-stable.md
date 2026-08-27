---
rg: 2
id: hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable
kind: claim
title: If SL2(Z[1/p]) is flexibly permutation-stable then the HNN extension centralizing SL2(Z) is not sofic
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that is the unitary statement with Hilbert--Schmidt norms and a conjugation spectral gap; this is the permutation statement with Hamming distance and Schreier-graph expansion, which Dogon--Vigdorovich's central-extension method does not have.
  openai-leavitt-unit-nonsofic: nonsofic groups are known unconditionally; this is a conditional structural statement whose interest is the mechanism and its unitary twin, not the existence of a nonsofic group.
---

Let `A = SL_2(Z[1/p])`, `C = SL_2(Z)`, `a_1 = diag(p, p^(-1))`, and

```text
G_p = < A, t | [t, c] = 1  (c in S_C) > = A *_C (C x Z).
```

**Theorem.**  If `A` is flexibly permutation-stable (every sofic
approximation of `A` is Hamming-close, after padding by a vanishing
fraction of points, to a sequence of genuine actions), then `G_p` is not
sofic.

*Proof.*  Two facts about the pair.  (i) Every finite action of `A` factors
through a congruence quotient `SL_2(Z/m)`, `gcd(m,p) = 1` (Serre's
congruence subgroup property), and `C` surjects onto it; so in every finite
action `rho` of `A` the permutation groups `rho(C)` and `rho(A)` coincide.
(ii) `C` has property `(tau)` for congruence quotients (Selberg): the
Schreier graphs of all congruence actions of `C`, and of their diagonal
actions on pairs, have Cheeger constant at least some `h > 0`.

Suppose `G_p` were sofic.  A sofic approximation restricted to `A` is,
after padding, `o(1)`-close to a genuine action `rho` of `A` on `[n]`; let
`sigma in Sym(n)` be the image of `t`.  The relators `[t, c] = 1` give
`d_Hamm(rho(c) sigma rho(c)^(-1), sigma) <= eps` for `c in S_C`.  The graph
`Gamma_sigma = {(i, sigma i)}` is then an `eps`-almost-invariant subset of
the finite `C`-set `[n] x [n]` (diagonal action, factoring through a
congruence quotient by (i)).  By (ii), on each orbit `O` the boundary of
`Gamma_sigma cap O` has size at least `h min(|Gamma_sigma cap O|,
|O \ Gamma_sigma|)`, so summing, `Gamma_sigma` is within `2|S_C| eps n / h`
points of a `C`-invariant subset `Gamma'`, which is a partial permutation
`sigma'` commuting with `rho(C)` on its domain.  By (i) `rho(a_1) in
rho(C)`, so `sigma'` commutes with `rho(a_1)` as well, hence
`d_Hamm([sigma, rho(a_1)], id) = O(eps/h) -> 0`.  But `[t, a_1] != 1` in
`G_p` by Britton's lemma, and a sofic approximation moves almost every
point by a nontrivial element.  Contradiction. ∎

**Remarks.**  The unitary twin is
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` with the pair
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`.  Dogon--Vigdorovich
remark (arXiv:2506.20843 source, commented text after their permutational
variant) that their method "does not seem to have a permutational
analogue" and that "it would be interesting to find an amalgamated product
such as `SL_2(Z[1/p])` for which flexible permutation stability implies the
existence of non-sofic groups"; the HNN extension above is such an amalgam.
Since nonsofic groups are now known unconditionally, the content of this
statement is the mechanism and the contrapositive: if `G_p` is sofic,
`SL_2(Z[1/p])` is not flexibly permutation-stable.

The property of the pair actually used, in both versions, is only that
`rho(C) = rho(A)` for every finite-dimensional unitary representation
(resp. finite action) `rho` of `A`, plus `(tau)` for `C` on those
quotients.
