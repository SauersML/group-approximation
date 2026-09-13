---
rg: 2
id: envelope-coset-action-sofic-once-edge-coset-action-sofic
kind: claim
title: On INF the envelope's graph-coset action is sofic once the first rope's action on its edge cosets is sofic
artifacts:
  - research/artifacts/twisted-rope-rf-envelope-2026-09-13-part2.md
distinct_from:
  twisted-rope-envelope-coset-action-is-sofic: that is the envelope statement itself; this derives it from the first rope's edge coset action.
  first-rope-edge-coset-action-is-sofic: that is the remaining input, still open.
---

ESTABLISHED (unreviewed). Notation of
[[twisted-rope-is-a-central-rope-over-an-rf-envelope]], on `INF`.

**Theorem.** If `Gamma_e action Gamma_e/S_e` is sofic, then
`D_e action D_e/C_e` is sofic.

**Consequence.** Combined with (E6) there, `R_e` is sofic whenever
`Gamma_e` is sofic and `Gamma_e action Gamma_e/S_e` is sofic. By GKP Theorem
3.7, the same two hypotheses make the untwisted rope
`< Gamma_e, z | [z, S_e] = 1 >` sofic. So the twist adds no difficulty: the
final edge is exactly as hard as the first rope's action on its edge cosets.

**Proof outline** (artifact Section 2).

1. Separate `C_e` by the larger graphs
   `C_n = {(s,rho) : phi_n(rho) = phi_n(lambda s)}`, for finite quotients
   `phi_n` of `R-hat`. The step uses (S1) of
   [[separating-sofic-quotient-sets-make-an-action-sofic]].
2. Pass to the quotient `Gamma_e x Phi_n`.
3. Drop the finite factor by
   [[finite-commuting-extension-of-a-sofic-action-is-sofic]].
4. Split into orbits `Gamma_e/ker(mu_n)`.
5. Embed each orbit injectively and equivariantly in
   `Gamma_e/S_e x G-hat/M_n`, with `M_n <= H x H` of finite index.
6. Conclude by (S2), restriction to the diagonal, and (C1). `M_n` is
   separable in `G-hat` by (BCF2) of
   [[three-bridge-is-cyclic-fiber-product-with-finite-cep]] and the modular
   law.

DERIVATION [[envelope-coset-action-sofic-once-edge-coset-action-sofic-proof]].
