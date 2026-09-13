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
- **Separation by larger graphs (done, landed).** Let `phi_n` be separating
  finite quotients of `R-hat`, and take the graphs
  `C_n = {(s,rho) : phi_n(rho) = phi_n(lambda s)}`. This separation, a
  commuting finite factor, and an injective map into
  `Gamma_e/S_e x G-hat/M_n` reduce this claim to
  [[first-rope-edge-coset-action-is-sofic]]. The reduction is
  [[envelope-coset-action-sofic-once-edge-coset-action-sofic]].
