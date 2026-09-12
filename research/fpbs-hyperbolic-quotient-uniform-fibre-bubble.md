---
rg: 2
id: fpbs-hyperbolic-quotient-uniform-fibre-bubble
kind: claim
title: Below criticality the fibre-summed two-point profile over a hyperbolic quotient is uniformly square summable
distinct_from:
  fpbs-amenable-wq-normal-relative-subcriticality: that asks for finiteness of the single diagonal entry E_p|K_o ∩ H| at some p above p_c and is equivalent to the threshold gap; this asks for a uniform l2 bound on the whole coset profile for p below p_c, which bounds that entry only at p_c.
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**OPEN.** For every finitely generated `Gamma` with an infinite normal
subgroup `H` such that `Q = Gamma/H` is non-elementary word hyperbolic, and
every finite symmetric generating set `S`,

```text
sup_{p < p_c(Cay(Gamma,S))}  sum_{q in Q} sigma_p(q)^2  <  infinity,
where sigma_p(q) = E_p|K_o ∩ q|.
```

This is premise (i) of `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap`. By
`fpbs-fibre-bubble-forces-mean-field-susceptibility` it already gives
`chi_p ≍ (p_c-p)^(-1)`, and it gives `E_(p_c)|K_o ∩ H| < infinity`.

Each `sigma_p(q)` is nondecreasing and left-continuous in `p`, being a supremum
of finite-volume connection probabilities. By monotone convergence the supremum
equals the critical fibre bubble, so the claim is the single critical statement
`sum_q sigma_(p_c)(q)^2 < infinity`. On tree-projected generating sets it is
implied by `fpbs-tree-projected-critical-sphere-bubble-below-one`.

## Attempts

* **From the L2 conjecture (not a proof).** For amenable `H`, the fibre bubble
  equals `||S_p delta_1||^2 <= ||T_p||^2`
  (`fpbs-fibre-summed-connectivity-operator`). So this claim follows from
  `fpbs-nonamenability-bounds-critical-connectivity-operator` but is weaker than
  it. **Where it stops:** the premise is the stronger conjecture.
* **Differential inequality.** Russo plus BK give `dT_p/dp <= p^(-1) T_p A T_p`
  entrywise. Pushed forward,
  `d/dp sum_q sigma_p(q)^2 <= (2d/p) ||S_p|| sum_q sigma_p(q)^2`. **Where it
  dies:** the growth rate is the L2 quantity `||S_p||` itself, which is
  unbounded as `p -> p_c` unless the L2 conjecture holds.
* **Mean-field prediction.** For critical branching random walk, `sigma` is the
  Green function of the walk projected to `Q`, and
  `||G_Q(1,.)||_2 <= sum_n rho(Q)^n < infinity`. **Where it dies:** the
  comparison with branching random walk is a triangle-type input.
* **Tree-projected generating sets of `F_n x Z`.** Here fibres are cut sets, so
  `sigma_p(q) <= prod_j sigma_p(s_j)` along the geodesic word (Section 4.3 of the
  artifact). The claim would follow from bounded `E_p|K_o ∩ H|` together with
  `(2n-1) max_s sigma_p(s)^2 < 1` uniformly. **Where it stops:** that
  nearest-fibre bound is itself unproved, and FKG gives
  `sigma_p(s) >= p E_p|K_o ∩ H|`.
