---
rg: 2
id: fpbs-hp-relative-sharpness
kind: claim
title: Below the relative critical threshold the intersection with the subgroup has exponential tail
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
---

**ESTABLISHED (imported).** Let `G` be a Cayley graph of a finitely generated
group `Gamma` with `H <= Gamma` a subgroup, and let `K_o` be the cluster of the
identity. For each `p < p_c(H;G)` there is `c = c(p) > 0` with

```text
P_p(|K_o ∩ H| >= n) <= exp(-c n)     for every n >= 1.
```

In particular the relative susceptibility `E_p|K_o ∩ H|` is finite below the
relative critical threshold.

Hutchcroft--Pan, arXiv:2409.12283v1, Theorem 1.8 (relative sharpness of the
phase transition), read from the PDF on 2026-09-11. Its proof relativizes the
OSSS volume-tail proof of sharpness.

Status records an imported theorem, not independent mathematical verification.
