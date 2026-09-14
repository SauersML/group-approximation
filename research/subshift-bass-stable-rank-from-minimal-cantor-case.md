---
rg: 2
id: subshift-bass-stable-rank-from-minimal-cantor-case
kind: route
title: The subshift stable-rank question is the special case of the minimal Cantor stable-rank question
target: subshift-crossed-product-ring-has-bass-stable-rank-at-most-two
requires: [minimal-cantor-crossed-product-has-stable-rank-at-most-two]
---

An infinite minimal subshift `X ⊆ A^Z` is compact, metrizable and totally disconnected. It has no isolated points,
because an isolated point of a minimal system has a dense orbit of isolated points, which forces `X` to be finite. So
`X` is a Cantor set, and the shift is a minimal homeomorphism of it. Then `LC(X,K) ⋊_T Z` is an instance of the ring
in `minimal-cantor-crossed-product-has-stable-rank-at-most-two`, with `k = K`. So a bound `sr ≤ 2` there gives the
bound here.
