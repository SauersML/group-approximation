---
rg: 2
id: fpbs-normal-coset-fibre-mass-power-improvement
kind: claim
title: Below the relative threshold of a normal subgroup the fibre-mass profile at p is a power above one of the profile at any larger parameter
distinct_from:
  fpbs-normal-fibre-second-moment-maximal: that bounds the second coset moment by the subgroup's; this bounds every moment and exponential moment, and converts it with the thinning inequality into a power improvement between two parameters.
  fpbs-hp-relative-sharpness: that gives exponential tails on the subgroup itself; this transfers them uniformly to all cosets and uses them to compare parameters.
artifacts:
  - research/artifacts/fpbs-fibre-power-improvement-2026-09-17.md
---

**ESTABLISHED.** Let `G = Cay(Gamma,S)`, let `N` be a normal subgroup and `Q = Gamma/N`. Put
`sigma_p(q) = E_p|K_o ∩ Gamma_q|` and `A_q = {o <-> Gamma_q}`.

1. **All coset moments are maximal on `N`.** For every `p` and every `r >= 1`,
   `E_p|K_o ∩ Gamma_q|^r <= E_p|K_o ∩ N|^r`. So for `p < p_c(N;G)`, the tails of
   `|K_o ∩ Gamma_q|` decay exponentially, uniformly in `q`.
2. **Hitting profile.** For `p < p_c(N;G)` and `r > 1`,
   `P_p(A_q) <= sigma_p(q) <= C_r P_p(A_q)^(1-1/r)`.
3. **Power improvement.** For `p < p_c(N;G)`, `p < p' < 1` and
   `1 <= s < log p / log p'`, there is `C` with

   ```text
   sigma_p(q) <= C sigma_(p')(q)^s        for every q in Q.
   ```
4. **Exponent monotonicity.** Let `r*(p) = inf{r : sigma_p ∈ l^r(Q)}`. Then
   `p -> r*(p) log(1/p)` is nondecreasing on `(0, p_c(N;G))`.

No amenability, tree structure or nonunimodularity is used. Item 4 is the
fibre-summed form of Hutchcroft--Pan's `beta*_{p^theta} <= theta beta*_p`
(arXiv:2412.15895, Section 3), which they prove only on nonunimodular slab geometries.

Proof: artifact Theorems 1 and 2 and Corollaries 1.1 and 2.1.
* The proof of item 1 is the mass transport of
  `fpbs-normal-fibre-second-moment-maximal-proof`, with Hölder's inequality in
  place of Cauchy--Schwarz.
* Item 3 combines item 2 with Grimmett's thinning inequality
  `P_{p^theta}(A) >= P_p(A)^theta` for increasing `A`.

## Attempts

* **Hölder mass transport plus thinning (2026-09-17, artifact §1–2).** The full
  proof is in the artifact, so no step is left open. Possible next uses are an
  `l^r` version at `p_c` and slab geometries without a free quotient.
