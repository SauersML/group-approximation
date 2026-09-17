---
rg: 2
id: cocf-group-torsion-order-bounded-by-word-length
kind: claim
title: "In a co-context-free group, a torsion element of word length n has order at most 2^((mn^2+1)^2)"
distinct_from:
  bit-register-cloning-group-has-doubly-exponential-period-growth: that is a lower bound in one specific group; this is the general upper bound for coCF groups
---

**ESTABLISHED (unreviewed).** Route `cocf-group-torsion-order-bounded-by-word-length-citation`.

Let `G` be a group with finite generating set `S`, and suppose the co-word problem `coWP(G,S)` is context-free. Then
there is a constant `m = m(G,S)`, the number of variables in a Chomsky-normal-form grammar for `coWP(G,S)`, with the
following property. Every `g ∈ G` of finite order with `‖g‖_S = n ≥ 1` satisfies

`n · ord(g) ≤ 2^((m n^2 + 1)^2)`.

In particular the period growth satisfies `p_(G,S)(n) ≤ 2^((m n^2+1)^2)`, which is `exp(O(n^4))`.

Established by literature import (Bishop–Bodart–Issini–Perego, Thm 2.7(a) and its proof).
