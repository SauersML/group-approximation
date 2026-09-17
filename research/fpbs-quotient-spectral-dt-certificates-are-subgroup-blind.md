---
rg: 2
id: fpbs-quotient-spectral-dt-certificates-are-subgroup-blind
kind: claim
title: Schreier-quotient spectral DT certificates give finite relative susceptibility but are never easier than the absolute certificate, and equal it for amenable subgroups
distinct_from:
  fpbs-amenable-kernel-l2-gap-forces-fibre-bubble: that shows the L2 gap forces a finite critical fibre bubble; this shows a finite-volume relative spectral certificate forces the L2 gap near p, by a Kesten-type spectral radius comparison that holds for every subgroup.
  fpbs-hyperbolic-quotient-uniform-fibre-bubble: that is an open fibre-bubble premise over hyperbolic quotients; this is an unconditional equality of quotient and full spectral radii of finitely supported boundary measures, together with the relative Neumann-series bound.
  fpbs-spectral-dt-certificate-bounds-connectivity-operator: that is the absolute certificate bounding T_p; this is the relative certificate bounding chi^H_p, plus the proof that it never beats the absolute one.
artifacts:
  - research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md
---

**ESTABLISHED.** With `nu_{S,p}` as in
`fpbs-spectral-dt-certificate-bounds-connectivity-operator`, let `H <= Gamma`
be a subgroup, and `sp_{H\Gamma}(nu)` the spectral radius of
`(rho(nu) phi)(Hx) = sum_g nu(g) phi(Hxg)` on `l2(H\Gamma)`.

1. **Relative certificate.** If `sp_{H\Gamma}(nu_{S,p}) < 1`, then
   `E_p|K_o ∩ H| <= |S|^2 sum_k ||rho_{H\Gamma}(nu_{S,p})^k|| < infinity`, and
   the same holds on an open interval of parameters around `p`.
2. **Blindness.** For every nonnegative finitely supported `nu`:
   * `sp_Gamma(nu) <= sp_{H\Gamma}(nu)` for every subgroup `H`, by comparing
     return probabilities with a faithful-trace lemma;
   * equality holds when `H` is amenable, by Følner lifting.

**Obstruction.** On the whole hierarchy of finite-exploration spectral
certificates, passing to a quotient by a subgroup never helps.

* A relative certificate at `p` implies the absolute one, and hence
  `||T_p||_{2->2} < infinity`.
* For amenable wq-normal `H` the two coincide.

So any proof of `fpbs-amenable-wq-normal-relative-subcriticality` by such
certificates is a proof of `p_c < p_{2->2}` on the same graph. At `S = {o}` this
is Kesten's `rho(Gamma/H) = rho(Gamma)`, which killed the target's
"count open walks" attempt. That coincidence persists at every `S`.

Proofs: artifact Sections 4 and 5.
