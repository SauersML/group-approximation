---
rg: 2
id: fpbs-kesten-gap-via-profile-kesten-ratio
kind: route
title: Get the Kesten gap from the Gram bound and bounded size-biased Kesten ratios of critical cluster profiles
target: fpbs-percolation-kesten-normal-gap
requires:
  - fpbs-critical-profile-kesten-ratio-integrable
  - fpbs-normal-fibre-mass-cluster-gram-representation
  - fpbs-quotient-l2-threshold-sandwich
artifacts:
  - research/artifacts/fpbs-cluster-gram-fibre-operator-2026-09-17.md
---

Fix `Gamma`, an infinite normal subgroup `N` with nonamenable `Q = Gamma/N`, and
a finite symmetric generating set `S`.

1. The open premise gives
   `M := limsup_{p ↑ p_c} E_p[ ||lambda_Q(a)||^2/|K_o| ] < infinity`.
2. By item 4 of the Gram representation, `||sigma_(p_c)||_Q <= M`. This is
   critical fibre l2.
3. By item 6 of the sandwich (openness), `p_c < p^Q_(2->2)(N;G)`.
4. By item 4 of the sandwich, `p^Q_(2->2)(N;G) <= p_c(N;G)`, since `N` is
   infinite. Hence `p_c(G) < p_c(N;G)`.

The route loses information in step 2. The Gram bound is an inequality, so the
premise is strictly stronger than critical fibre l2. What the route gains is
that the premise concerns the shadow of each cluster separately.

By Section 2 of the artifact, the premise cannot come from invariant-percolation
axioms alone.
