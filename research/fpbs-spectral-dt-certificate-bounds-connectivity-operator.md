---
rg: 2
id: fpbs-spectral-dt-certificate-bounds-connectivity-operator
kind: claim
title: A finite set whose Duminil-Copin–Tassion boundary measure has convolution spectral radius below one bounds the connectivity operator, and the condition is open in p
distinct_from:
  fpbs-critical-sphere-fibre-operator-below-one: that asks for one sphere-restricted operator built from the full critical two-point function over a hyperbolic quotient with rapid decay; this uses connection probabilities inside a finite set, the spectral radius instead of the norm, any group, and proves the bound on T_p directly in finite volume.
  fpbs-l2-gap-class-closed-under-local-limits: that uses the DT mass phi_p(S) < 1 to show the l2 gap class is closed under local limits; this replaces the mass by the spectral radius of the boundary measure and proves that criterion bounds T_p.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that conjectures ||T_(p_c)|| < infinity on every nonamenable graph; this gives a finite-volume sufficient certificate for it and proves nothing about which graphs admit one.
artifacts:
  - research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md
---

**ESTABLISHED.** Let `G = Cay(Gamma, D)`, and `S` a finite vertex set
containing `o`. Put

```text
nu_{S,p}(g) = p * sum_{ {u,v} in Delta S, v = g } P_p(o <->_S u),
```

where `Delta S` is the set of edges leaving `S` and `<->_S` means connection
inside `S`. Let `sp_Gamma(nu)` be the spectral radius of convolution by `nu` on
`l2(Gamma)`.

1. **Bound.** If `sp_Gamma(nu_{S,p}) < 1`, then
   `||T_p||_{2->2} <= |S| sum_k ||rho_Gamma(nu_{S,p})^k|| < infinity`.
2. **Openness.** For fixed `S`, the set of such `p` is an open interval
   `(0, p_S)`.
3. **Threshold.** `p_sDT := sup_S p_S` satisfies `p_c <= p_sDT <= p_{2->2}`. So
   a certificate at `p_c`, meaning `p_c < p_sDT`, gives `p_c < p_{2->2}` and
   `||T_(p_c)|| < infinity`.
4. **Calibration.**
   * `S = {o}` gives the classical level `p d rho < 1`.
   * On amenable groups the spectral radius equals the DT mass, so no
     certificate exists at `p_c`.
   * On the 3-regular tree, `B_3` is a critical certificate, and balls give
     `p_sDT = p_{2->2} = 1/sqrt 2`.

Proofs: artifact Sections 2, 3 and 6.

*Novelty.* Prior art in Hutchcroft's L2 papers has not been excluded. The proof
is self-contained.
