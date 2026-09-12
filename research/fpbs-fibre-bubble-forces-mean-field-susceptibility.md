---
rg: 2
id: fpbs-fibre-bubble-forces-mean-field-susceptibility
kind: claim
title: A uniform fibre bubble over a hyperbolic quotient forces the mean-field susceptibility bound
distinct_from:
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that imports Hutchcroft's nonuniqueness theorem for Gromov hyperbolic graphs; this proves the susceptibility exponent bound for groups that are only hyperbolic modulo an infinite normal subgroup, under a fibre-diagram hypothesis.
  fpbs-sc-choi-seo: that covers acylindrically hyperbolic groups unconditionally; groups with an infinite normal subgroup and hyperbolic quotient, such as F_2 x Z, lie outside it, and this implication is conditional.
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**ESTABLISHED (implication).** Let `Gamma` be finitely generated, `H` an
infinite normal subgroup with `Q = Gamma/H` non-elementary word hyperbolic, and
`S` any finite symmetric generating set of `Gamma`. With
`sigma_p(q) = E_p|K_o ∩ q|` for cosets `q in Q`, suppose

```text
B = sup_{p < p_c} sum_{q in Q} sigma_p(q)^2 < infinity.
```

Then there is `C < infinity` with `chi_p = E_p|K_o| <= C (p_c - p)^(-1)` for
all `p < p_c`. This is the mean-field bound `gamma = 1` on the susceptibility
exponent.

Hutchcroft's Lemma 5.3 asks that half of every finite set be supported by a
halfspace. That condition fails for `Gamma` on fibre-concentrated sets
(Choi–Seo arXiv:2508.08932 Section 2.3). The proof counts fibres met instead,
using the supporting-hyperplane theorem on `Q`. The tree-graph inequality and
mass transport convert the fibre count back: `E_p|pi(K_o)| >= chi_p/(4B)`. The
rest of Hutchcroft's Proposition 5.1 runs unchanged on fibre-saturated
halfspaces with separated translates. Proof in Section 2 of the artifact.
