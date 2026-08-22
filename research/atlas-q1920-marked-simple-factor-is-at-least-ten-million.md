---
rg: 2
id: atlas-q1920-marked-simple-factor-is-at-least-ten-million
kind: claim
title: Every faithful full Q1920 carrier has a simple factor of order at least ten million
distinct_from:
  atlas-full-large-no-simple-quotient-under-million: that exhausts all simple targets below one million after only the order-360 filter; this uses normal generation by the binary module and a marked-subgroup census to reach ten million.
  atlas-sp6-canonical-moved-module-completion-fails: that treats the one Q1920 class in Sp6(2); this simultaneously handles every Q or Q modulo center embedding in all eligible simple groups below ten million.
---

Let `G` be a finite full completion which is faithful on one of the two marked
`Q1920` vertices.  Then every nontrivial simple quotient furnished by the
normal-generation reduction has order at least `10^7`.

## Attempts

Divisibility alone leaves fifteen targets below the bound.  The proof route
first removes ten which contain neither possible Q image, then exhausts the
finite ambient-normalizer twist sets for the remaining five.  Beyond this
bound an order-independent result requires a CFSG classification of marked
`2^4:A5` and `2^5:A5` overgroups; no such classification is inferred from
the finite census.
