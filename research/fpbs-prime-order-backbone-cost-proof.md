---
rg: 2
id: fpbs-prime-order-backbone-cost-proof
kind: route
title: Use two noncommuting prime-order powers as the cyclic backbone in an augmented generating set
target: fpbs-prime-divisor-upper-cost
requires:
  - fpbs-action-level-local-expanding-sparsifiers
  - fpbs-burnside-embedding-input
artifacts:
  - research/artifacts/fpbs/local-sparsifiers.md
  - research/artifacts/fpbs/scripts/replay_local_sparsifiers.py
  - research/artifacts/fpbs/local-sparsifier-checks.json
---

Section 10. The powers a_1^(n/p), a_2^(n/p) have order p and do not commute: C(a_1^(n/p))=<a_1>, whereas the two cyclic generator subgroups have trivial intersection by abelianization. Adjoin the two powers to a finite generating set and apply the original-action construction. Each cyclic part costs 1-1/p and the other generators cost at most epsilon. Take the graphing infimum. No original-edge claim is made for the sharper bound.

This route records a written proof or cited input; Cairn does not independently verify mathematics.
