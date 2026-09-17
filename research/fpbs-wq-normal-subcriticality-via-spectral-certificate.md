---
rg: 2
id: fpbs-wq-normal-subcriticality-via-spectral-certificate
kind: route
title: A critical spectral DT certificate transfers to the Schreier space of the amenable subgroup and is open, giving finite relative susceptibility above p_c
target: fpbs-amenable-wq-normal-relative-subcriticality
requires:
  - fpbs-wq-normal-class-critical-spectral-dt-certificate
  - fpbs-quotient-spectral-dt-certificates-are-subgroup-blind
artifacts:
  - research/artifacts/fpbs-spectral-dt-certificate-2026-09-17.md
---

1. **Critical certificate.** By
   `fpbs-wq-normal-class-critical-spectral-dt-certificate`, some finite `S` has
   `sp_Gamma(nu_{S,p_c}) < 1`.
2. **Transfer to the Schreier space.** `H` is amenable, so
   `sp_{H\Gamma}(nu_{S,p_c}) = sp_Gamma(nu_{S,p_c}) < 1` by the equality in
   `fpbs-quotient-spectral-dt-certificates-are-subgroup-blind`.
3. **Finite relative susceptibility.** The relative certificate of the same
   claim is open in `p`. So there is `p > p_c` with
   `sp_{H\Gamma}(nu_{S,p}) < 1`, and it gives `E_p|K_o ∩ H| < infinity`.

This removes the openness obstruction of the target's Attempt 4.4. The whole
remaining difficulty sits in step 1. That step is H-blind and implies the
critical L2 bound on these graphs, so this route cannot beat the L2 approach.
It replaces that approach by a finite-volume statement.
