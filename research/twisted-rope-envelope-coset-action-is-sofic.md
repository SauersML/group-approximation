---
rg: 2
id: twisted-rope-envelope-coset-action-is-sofic
kind: claim
title: The coset action of Gamma_e times the envelope on the twisted edge's graph cosets is sofic
distinct_from:
  product-of-free-groups-set-actions-are-sofic: that concerns actions of F x F', which carry the first rope; this is one action of Gamma_e x R-hat, which carries the second rope.
  twisted-rope-sofic-once-first-rope-sofic: that is soficity of the twisted rope itself; this is the set-action input that implies it through GKP Theorem 3.7.
---

OPEN. Use the notation of
[[twisted-rope-is-a-central-rope-over-an-rf-envelope]], on `INF`:

- `D_e = Gamma_e x R-hat`;
- `C_e = { (s, (Lambda(s), 1)) : s in S_e }`, the graph of
  `lambda = (Lambda, 1) : S_e -> R-hat`.

The claim: if `Gamma_e` is sofic, then `D_e action D_e/C_e` is a sofic action
in the sense of GKP Definition 2.1(5).

With [[twisted-rope-is-a-central-rope-over-an-rf-envelope]] (E6) it gives
[[twisted-rope-sofic-once-first-rope-sofic]].

## Attempts

- **Fibration (structure, verified).** `(g, rho)C_e |-> gS_e` is
  `D_e`-equivariant onto `Gamma_e/S_e`. Its fibre over `S_e` is a copy of
  `R-hat`, since `(s,rho)C_e = (1, rho lambda(s)^-1)C_e`. The stabilizer
  `S_e x R-hat` acts on the fibre by `(s,rho).x = rho x lambda(s)^-1`. That is
  the pullback of the two-sided action `R-hat x R-hat action R-hat`. So
  `D_e/C_e` is induced, over the base action `Gamma_e action Gamma_e/S_e`, from
  a pulled-back two-sided action of a residually finite group. The attempt dies
  for lack of an induction theorem for sofic set actions. A model of
  `G action G/K` carries no `K`-valued cocycle labels to glue fibre models
  along.
- **Separation by larger graphs (reduction, unchecked).** Let
  `phi_n : R-hat -> Phi_n` be separating finite quotients, and set
  `C_n = {(s, rho) : phi_n(rho) = phi_n(lambda s)}`. Then `C_e` is the
  intersection of the `C_n`, and `D_e action D_e/C_n` factors through
  `Gamma_e x Phi_n` acting on the cosets of the graph of the finite-image map
  `mu_n = phi_n lambda`. By (S1) of
  [[separating-sofic-quotient-sets-make-an-action-sofic]], it suffices that
  every such finite-graph action is sofic. Each finite-graph coset space is a
  quotient of `Gamma_e/ker(mu_n) x Phi_n` by a free action of the finite
  group `mu_n(S_e)`. No recorded result passes soficity to such a quotient.
  With one, the claim would reduce to soficity of
  `Gamma_e action Gamma_e/S''` for the finite-index subgroups
  `S'' = ker(mu_n)` of `S_e`.
- **The base action.** No recorded result covers
  `Gamma_e action Gamma_e/S_e`. `S_e` contains `F`, and by
  [[compiler-rope-edge-is-not-co-amenable]] (R1) the quotient `F/N_e` is
  non-amenable. Whether `S_e` is co-amenable in `Gamma_e` has not been
  checked.
