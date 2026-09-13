---
rg: 2
id: rp-fp-n-hosts-from-type-fn-plus-1-hosts
kind: route
title: "F_{n+1} hosts for all groups of type F_n give recursively presented FP_n hosts at every finite level"
target: every-fg-rp-group-has-rp-fp-n-hosts-for-each-finite-n
requires:
  - every-type-fn-group-embeds-in-a-type-fn-plus-1-group
  - mikaelian-explicit-higman-embedding
---

Let `Q` be finitely generated and recursively presented, and let `n >= 1`.
By Higman's embedding theorem (second required claim), `Q` embeds in a
finitely presented group `K_2`, which is of type `F_2`. Applying the first
required claim `n - 2` times, when `n >= 3`, gives
`K_2 <= K_3 <= ... <= K_n` with `K_m` of type `F_m`. Put `K_n = K_2` when
`n <= 2`. Then `K_n` is finitely presented, hence recursively presented, and
of type `FP_n`, and `Q <= K_n`.

Together with `type-fn-plus-1-hosts-via-rp-fp-n-hosts` this records an
equivalence, so the dependency cycle is intended.
