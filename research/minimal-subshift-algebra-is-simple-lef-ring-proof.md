---
rg: 2
id: minimal-subshift-algebra-is-simple-lef-ring-proof
kind: route
title: Cut an ideal down to a small cylinder, and model the ring on primitive periodic return words
target: minimal-subshift-algebra-is-simple-lef-ring
requires: []
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
---

Complete derivation in the artifact, Part 1, §1.1--1.4 and §3.1--3.2.

**Generators.** `u^i chi_[x_0=a] u^(-i) = chi_[x_(-i)=a]`. Products of these give every cylinder,
and sums give `LC(X,F_q)`.

**Simplicity.** Take `0 != P = sum_j f_j u^j` in an ideal `J`, with `f_0(x) = c != 0`. `X` has no
periodic point, so a clopen `W ∋ x` with `f_0 = c` on `W` and `T^j W ∩ W = ∅` for the finitely many
`j != 0` in the support gives `chi_W P chi_W = c chi_W ∈ J`. Minimality covers `X` by finitely many
translates `T^i W`. Each `chi_(T^i W) = u^i chi_W u^(-i)` lies in `J`, and inclusion-exclusion gives
`1 ∈ J`.

**Centre.** Commuting with every `chi_W` kills `f_j` for `j != 0`, by freeness. Commuting with `u`
makes `f_0` shift-invariant, hence constant by minimality.

**LEF.** By uniform recurrence, choose two occurrences of a word `v` of length `2k` in a point `x`,
at distance `N_k >= max(2k+1, l(2k+1))`, and put `w_k = x_[p,p')`.
- A cyclic window of `w_k^infinity` of length `<= 2k+1` either lies inside `w_k` or equals
  `x_[p'-s, p'+t)`, because `v` is a prefix of `w_k` and `x_[p,p'+2k) = w_k v`. So all cyclic
  windows are words of `X`.
- Every word of `L_(2k+1)(X)` occurs in `w_k`.

Map `f u^j` to `D_k(f) P_k^j`, where `P_k` is the cyclic shift and `D_k(f)` reads `f` on the
cyclic windows. This is well defined, because windows lie in `L(X)`. It is multiplicative, because
`P^i D(g) P^(-i)` is the model of `g o T^(-i)`. It is injective, because a nonzero coefficient is
nonzero on some word of `X`, which occurs in `w_k`, and distinct `u`-degrees have disjoint supports
once `N_k > 2 max|j|`. Passing to the ultraproduct gives an injective unital ring homomorphism.
