---
rg: 2
id: fpbs-hyperbolic-quotient-fibre-estimates-l2-gap
kind: claim
title: Two fibre estimates over a hyperbolic quotient give p_c < p_2->2 on every Cayley graph
distinct_from:
  fpbs-critical-l2-implies-nonuniqueness: that imports Hutchcroft's implication from critical L2 boundedness to nonuniqueness; this derives the L2 gap itself from two fibre estimates on groups that are hyperbolic modulo an infinite normal subgroup.
  fpbs-fibre-bubble-forces-mean-field-susceptibility: that gives only the susceptibility bound from the fibre bubble; this adds the far-halfspace share and concludes p_c < p_{2->2}, hence the nonuniqueness phase.
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

**ESTABLISHED (implication).** Let `Gamma` be finitely generated, `H` an
infinite normal subgroup with `Q = Gamma/H` non-elementary word hyperbolic, and
`S` any finite symmetric generating set. Let `sigma_p(q) = E_p|K_o ∩ q|` and
let `Phi : Q -> H^d` be a rough similarity onto a coarsely dense subset of a
closed convex set. Suppose both of the following hold.

* **(i) Uniform fibre bubble.** `sup_{p<p_c} sum_q sigma_p(q)^2 < infinity`.
* **(ii) Vanishing far-halfspace share.** `sh(D) -> 0` as `D -> infinity`,
  where

  ```text
  sh(D) = sup_{p<p_c} sup_{a in Q} sup_{halfspaces H, d(Phi(a),H) >= D}
          chi_p^(-1) sum_{q in Phi^(-1)(H)} sigma_p(a^(-1) q).
  ```

Then `p_c(Cay(Gamma,S)) < p_{2->2}(Cay(Gamma,S))`. Consequently
`p_c < p_u` and the triangle condition holds at `p_c`.

*Proof sketch.*
1. Cheeger's inequality for the stochastic matrix `S_p/chi_p` on `Q`, together
   with Hutchcroft's hyperbolic magic lemma, bounds `1 - iota(S_p)` by
   `eps + N(eps) B^(1/2) / chi_p + 2 sh(1/eps)`. This tends to 0 as `p`
   increases to `p_c`.
2. `||T_p|| <= ||S_p||` by `fpbs-fibre-summed-connectivity-operator`, and
   `(p_c-p) chi_p <= C` by `fpbs-fibre-bubble-forces-mean-field-susceptibility`.
   So `(p_c-p)||T_p|| -> 0`.
3. Hutchcroft's Corollary 2.6 then gives `p_c < p_{2->2}`.

Amenability of `H` is not used. Proof in Section 3 of the artifact.
