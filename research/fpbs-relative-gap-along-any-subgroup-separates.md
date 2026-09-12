---
rg: 2
id: fpbs-relative-gap-along-any-subgroup-separates
kind: claim
title: A relative threshold gap along any infinite subgroup separates the global thresholds
distinct_from:
  fpbs-bs-iff-finite-relative-susceptibility: that is an equivalence for an infinite amenable wq-normal subgroup, whose relative critical threshold equals p_u; this gives only the sufficient direction, but for an arbitrary infinite subgroup with no amenability or wq-normality, through the inequality p_c(I;G) <= p_u(G).
  fpbs-amenable-wq-normal-pu-is-relative-pc: that identifies p_u with the relative critical threshold of an amenable wq-normal subgroup; this proves only the one-sided inequality p_c(I;G) <= p_u(G), but for every infinite subgroup.
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**ESTABLISHED.** Let `G = Cay(Gamma,S)` for a finitely generated group `Gamma`,
and let `I <= Gamma` be any infinite subgroup. Write
- `p_c(I;G)` and `p_u(I;G)` for Hutchcroft--Pan's relative thresholds, i.e. the
  thresholds for existence and for uniqueness of a cluster meeting `I` in
  infinitely many vertices;
- `chi^I_p = E_p|K_o ∩ I|`.

Then

```text
p_c(I;G) <= p_u(I;G) <= p_u(G).
```

Moreover the following are equivalent, and each implies `p_c(G) < p_u(G)`:

1. `p_c(G) < p_c(I;G)`;
2. `chi^I_p < infinity` for some `p > p_c(G)`.

So to separate the thresholds of one Cayley graph, it is enough to find one
infinite subgroup that slightly supercritical clusters meet only finitely often
in expectation. The subgroup need not be normal, commensurated, wq-normal or
amenable.

The proof is in `fpbs-relative-gap-along-any-subgroup-separates-proof`; see also
Section 7 of the artifact.
