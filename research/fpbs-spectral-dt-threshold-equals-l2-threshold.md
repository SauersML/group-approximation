---
rg: 2
id: fpbs-spectral-dt-threshold-equals-l2-threshold
kind: claim
title: The spectral Duminil-Copin–Tassion threshold equals p_(2->2), so critical L2 boundedness holds iff some critical ball boundary measure has convolution norm below one
distinct_from:
  fpbs-spectral-dt-certificate-bounds-connectivity-operator: that proves certificates bound T_p and p_sDT <= p_(2->2), and leaves the converse open in its artifact Section 7; this proves the converse, p_sDT = p_(2->2), with balls of explicit radius.
  fpbs-sphere-fibre-operator-iff-critical-fibre-l2: that characterises critical L2 by one sphere-restricted operator built from the full two-point function; this characterises it by finite-volume DT boundary measures, whose coefficients are polynomials in p.
  fpbs-wq-normal-class-critical-spectral-dt-certificate: that asks for a critical certificate on a class; this shows that request is equivalent to p_c < p_(2->2) on each graph of the class.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is the universal conjecture; this proves nothing universal, it gives an exact finite-volume form of it.
artifacts:
  - research/artifacts/fpbs-spectral-dt-threshold-equals-p22-2026-09-17.md
---

**ESTABLISHED.** Let `G = Cay(Gamma, D)`, and `nu_{S,p}` the DT boundary measure
of `fpbs-spectral-dt-certificate-bounds-connectivity-operator`. Put
`B_R = {|x| <= R}` and `N_p = ||T_p||_{2->2}`.

1. **Bound.** If `N_p < infinity`, then for all `R >= 0`,
   ```text
   sp(rho_Gamma(nu_{B_R,p})) <= ||rho_Gamma(nu_{B_R,p})|| <= p |D| e N_p exp(-R/(e N_p)).
   ```
2. **Thresholds.** `p_sDT(G) = p_{2->2}(G)`.
3. **Finite-volume form.** The following are equivalent:
   * `||T_{p_c}|| < infinity`;
   * `p_c < p_{2->2}`;
   * some finite `S` containing `o` has `sp(rho(nu_{S,p_c})) < 1`;
   * some ball has `||rho(nu_{B_R,p_c})|| < 1`.

   At `p_c` every such measure has mass `phi_{p_c}(S) >= 1` (DT). So
   Hutchcroft's conjecture is a mass-versus-norm gap for one explicit family of
   finitely supported measures.
4. **Zero-one law.** Either the critical ball norms decay exponentially in `R`,
   or `sp(rho(nu_{S,p_c})) >= 1` for every finite `S`.
5. **Collapse of a prerequisite.** `fpbs-wq-normal-class-critical-spectral-dt-certificate`
   is equivalent, graph by graph, to `p_c < p_{2->2}` on its class. Its failure
   mode "`p_sDT < p_{2->2}`" cannot occur.

Proof: artifact Sections 2 and 3. The bound is two positive-kernel steps.
First, the ball boundary measure is at most `p (tau_p 1_{S_R}) * a_D`. Second,
the tail bootstrap of `fpbs-sphere-fibre-operator-iff-critical-fibre-l2` (the
`H = {1}` case of Hutchcroft's Proposition 2.4) makes that sphere operator
exponentially small.
