---
rg: 2
id: fpbs-tree-projected-critical-sphere-bubble-below-one
kind: claim
title: Some critical fibre-sphere bubble of a tree-projected Cayley graph is below one
distinct_from:
  fpbs-hyperbolic-quotient-uniform-fibre-bubble: that asks for finiteness of the whole critical fibre bubble over any hyperbolic quotient; this asks, on tree-projected generating sets only, that one finite sphere of the quotient carry critical squared fibre mass below one.
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**OPEN.** Let `Gamma`, `H = <z>` and `S` be as in
`fpbs-tree-projected-sphere-bubble-l2-equivalence`: `Gamma/H = F_n`, and the
image of `S` lies in a free basis, its inverses and `1`. Then there is `R >= 1`
with

```text
b_R(p_c) = sum_{q in S_{F_n}(R)} ( E_(p_c)|K_o ∩ q| )^2  <  1.
```

By submultiplicativity this is equivalent to exponential decay of the critical
fibre-sphere bubble, `lim_R b_R(p_c)^(1/R) < 1`. By
`fpbs-tree-projected-sphere-bubble-l2-equivalence` it is equivalent to
`p_c < p_{2->2}` on `Cay(Gamma,S)`.

## Attempts

* **Mean-field prediction.** Critical branching random walk projected to the
  tree gives `sigma(q) ≈ chi^H lambda^|q|` with `(2n-1) lambda = 1`, so
  `b_R ≈ (chi^H)^2 (2n-1)^(-R) -> 0`. **Where it stops:** this is the triangle-type
  comparison that is not available.
* **Split into sphere mass and maximum.**
  `b_R <= max_(|q|=R) sigma(q) · E_(p_c)|K_o ∩ pi^(-1) S(R)|`. **Where it dies:**
  neither factor is controlled at `p_c`. Boundedness of the sphere mass is a
  mean-field statement, and decay of the maximal fibre mass along the tree is
  as hard as the claim.
* **Differential inequalities.** Russo and BK bound the growth of `b_R` in `p`
  by the L2 quantity `||S_p||`. **Where it dies:** the bound is circular (see
  `fpbs-hyperbolic-quotient-uniform-fibre-bubble`).
* **Sharper cut bounds.** Last-crossing decompositions remove the per-step
  spreading loss of first-hit BK and give branch shares through half-graph
  relative susceptibilities (lane bs-pc-pu-2). **Where it stops:** those bounds
  still need a critical input below one.
