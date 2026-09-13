---
rg: 2
id: twisted-rope-is-a-central-rope-over-an-rf-envelope
kind: claim
title: On INF the compiler's twisted rope embeds in a central rope over Gamma_e times one fixed residually finite group
artifacts:
  - research/artifacts/twisted-rope-rf-envelope-2026-09-13.md
distinct_from:
  asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope: that is the embedding for any overgroup in which the twist is inner; this constructs such an overgroup for the compiler's twisted rope, explicit, e-independent and residually finite, and draws the sofic consequence.
  regular-mf-tensor-sync-proves-twisted-rope-mf: that implements the twist in a norm reduced product whose finite factor kills K_e^0; this implements it inside one group, with no approximation.
  compiler-rope-edge-is-not-co-amenable: its Consequences say no recorded result covers the twisted rope; this places that rope inside a free generalized wreath product over a single coset action.
---

ESTABLISHED (unreviewed). Notation of
`research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`, items 3--8,
on `INF`:

- `P = F_2 x F_2` and `H = B3(1) = ker chi <= P` (BCF1 of
  [[three-bridge-is-cyclic-fiber-product-with-finite-cep]]);
- `Q_e = H`, the first rope `Gamma_e = < K_e, v | [v, L_e] = 1 >`;
- the edge `S_e = F *_(N_e) F^v`;
- the twisted rope
  `R_e = < Gamma_e x H, u | u(s,1)u^-1 = (s, tau_e(s)), s in S_e >`.

1. **(L1) Group-level fold.** `Lambda : Gamma_e -> G-hat = (P x P) x| <sigma>`,
   killing `K_e^0`, `(f,p) in K^g |-> (q_+(f), p)`, `v |-> sigma`, is a
   homomorphism. Its restriction to `S_e` lands in `H x H`, with
   `tau_e = pr_1 o Lambda` on `S_e`. The finite maps `lambda_n` of (RTS1) are
   `r_n o Lambda`.
2. **(E1) Envelope.**
   `R-hat = < G-hat x H, w | w(s,1)w^-1 = (s, pr_1 s), s in H x H >` is
   residually finite. It is independent of `e`.
3. **(E2)--(E3) Inner twist.** `iota(g,q) = (g, (Lambda(g), q))` embeds
   `Gamma_e x H` in `D_e = Gamma_e x R-hat`, and `(1,w)` conjugates
   `iota(s,1)` to `iota(s, tau_e(s))` for every `s in S_e`.
4. **(E4) Embedding.** `R_e` embeds in
   `Omega_e = < D_e, z | [z, C_e] = 1 >` via `u -> (1,w) z`, where
   `C_e = iota(S_e x 1) ~= S_e`.
5. **(E5) Wreath form.** `Omega_e ~= Z wr^*_(D_e action D_e/C_e) D_e`.
6. **(E6) Sofic criterion.** If `Gamma_e` is sofic and the coset action
   `D_e action D_e/C_e` is sofic (GKP Definition 2.1(5)), then `R_e` is sofic.

So the non-identity associated isomorphism is not an obstruction to soficity.
It is inner in a fixed residually finite overgroup. The remaining input is the
coset action in item 6, [[twisted-rope-envelope-coset-action-is-sofic]].

DERIVATION [[twisted-rope-is-a-central-rope-over-an-rf-envelope-proof]].
