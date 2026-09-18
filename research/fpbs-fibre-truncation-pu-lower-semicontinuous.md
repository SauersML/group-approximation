---
rg: 2
id: fpbs-fibre-truncation-pu-lower-semicontinuous
kind: claim
title: The uniqueness threshold is lower semicontinuous along a fibre-truncation tower of an amenable normal subgroup
distinct_from:
  fpbs-fibre-truncation-towers-add-no-slack: that proves monotone convergence of fibre occupations and needs no hypothesis on H; this uses amenability of H with relative sharpness and Harris-FKG to force nonuniqueness on the truncations, giving p_u(G) <= liminf p_u(G_k).
  fpbs-amenable-wq-normal-pu-is-relative-pc: that identifies p_u(G) with the relative critical threshold on one graph; this compares p_u across the tower of quotients Gamma/H_k.
artifacts:
  - research/artifacts/fpbs-fibre-truncation-towers-2026-09-17.md
---

**ESTABLISHED.** Let `H` be an infinite amenable normal subgroup of a finitely
generated group `Gamma`. Let `(H_k)` be a fibre-truncation tower as in
`fpbs-fibre-truncation-towers-add-no-slack`: normal in `Gamma`, of finite index
in `H`, nested, with trivial intersection. Let `G = Cay(Gamma,S)` and
`G_k = Cay(Gamma/H_k, S_k)`. Then

```text
p_u(G)  <=  liminf_(k -> infinity) p_u(G_k).
```

**Quantitative form.** Suppose `p > p_c(G_(k_1))` and
`chi^H_G(p) = E_p|K_o ∩ H| < infinity`. Then `p <= p_u(G_k)` for every
`k >= k_1` with `[H:H_k] theta_(G_(k_1))(p)^2 > chi^H_G(p)`.

**Corollary (necessary uniform gap, and a counterexample detector).** If
`p_c(G) < p_u(G)`, then `liminf_k p_u(G_k) >= p_u(G) > p_c(G)`, while
`p_c(G_k) >= p_c(G)`. So a fibre tower along which `p_u(G_k)` approaches
`p_c(G)` on a subsequence would be a counterexample to the Benjamini--Schramm
conjecture for `G`. For one-ended hyperbolic quotients `Gamma/H`, such as
surface groups times `Z` and Seifert-fibred groups, this condition is not
automatic.

**Where per-truncation gap theorems die.**

* **The step.** A gap theorem on `G_k` concludes a lower bound on `p_u(G_k)`.
  Turning that into a lower bound on `p_u(G)` needs upper semicontinuity of
  `p_u` along the tower. The theorem above gives only lower semicontinuity.
* **Calibration (recorded, not claimed).** For `F_2 x Z` with standard
  generators, `p_u(G_k) = 1` for every `k`, while `p_u(G) < 1`. This uses two
  theorems that are not imported into the graph: "infinitely many ends implies
  `p_u = 1`", and Babson--Benjamini, "one-ended finitely presented implies
  `p_u < 1`".
* **Consequence.** The uniform-gap condition holds automatically for virtually
  free quotients. So "a uniform truncation gap implies the hole" would by
  itself settle `F_2 x Z` on every generating set.

**Proof.** `fpbs-fibre-truncation-pu-lower-semicontinuous-proof`.
