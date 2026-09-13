---
rg: 2
id: group-factor-local-universality-ultraproduct-proof
kind: route
title: Collect one group per rational moment table and take their free product
target: group-factor-local-universality-reduces-to-ultraproducts
requires: []
---

**Moment tables.**  For `k >= 1`, a level-`k` table is a function `t` from the
finite set `P_k` of *-monomials of degree at most `k` in `k` noncommuting
variables to `Q(i)`.  There are countably many tables.  Say a tracial von
Neumann algebra `M` realizes `t` within `eps` if there are contractions
`b_1..b_k in M` with `|sigma(m(b)) - t(m)| < eps` for all `m in P_k`.

**Lemma M** (moments determine the embedding) is proved on route
`locally-universal-group-factor-nonhyperlinear-proof`: contractions in an
ultraproduct with exactly the moments of generators of `N` generate a copy of
`N`, trace-preservingly.

**(1) ⟹ (2).**  Take `Gamma_n = U` for all `n` and `V = omega`.

**(2) ⟹ (1).**
1. For every level-`k` table `t` that is realized within `1/(2k)` by some
   group factor `L(Gamma)` of a countable group, choose one such group
   `Gamma_t`.  Let `U` be the free product of all chosen `Gamma_t`.  It is a
   countable group, and each `Gamma_t <= U` gives a trace-preserving inclusion
   `L(Gamma_t) subset L(U)`.
2. Let `N` be separable with contraction generators `a_1, a_2, ...`.  Fix `k`.
   By (2), `N` embeds in some `prod_V L(Gamma_n)`; lifting the images of
   `a_1..a_k` to contractions shows that the level-`k` moment table of `a`
   is realized within `1/(4k)` by some `L(Gamma_n)`.
3. Choose a rational table `t` within `1/(4k)` of the moment table of `a`.
   Step 2 shows `t` is realized within `1/(2k)` by a group factor, so
   `Gamma_t` exists and realizes `t` within `1/(2k)`.  Hence `L(U)` realizes
   the moment table of `a` within `3/(4k) < 1/k`.
4. For each `k` pick such contractions `b^(k)` in `L(U)`.  In `L(U)^W` for a
   nonprincipal ultrafilter `W` on `N`, the tuple `[(b^(k))_k]` has exactly the
   moments of `a`, so Lemma M embeds `N` into `L(U)^W` unitally and
   trace-preservingly.

So `L(U)` is locally universal.
