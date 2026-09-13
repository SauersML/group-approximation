---
rg: 2
id: bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host
kind: claim
title: BS(1,2) embeds in a finitely presented simple Röver–Nekrashevych group over a host with quadratic Dehn function
distinct_from:
  twisted-btb-groups-poly-dehn-only-if-np-eq-conp: that rules out twisted Brin–Thompson envelopes on infinite sets under NP != coNP, through 2V; this is a Röver–Nekrashevych envelope, and whether 2V embeds in it is not addressed here.
  cornulier-tessera-host-is-rational-weakly-diagonal-self-similar: that is the host and its self-similar action; this is the simple envelope built from it and the embedding of the host into the envelope's commutator subgroup.
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

**ESTABLISHED** through `bs12-rn-envelope-via-zaremsky-corollary-proof`. Not
independently reviewed.

**Claim.** Let `Gamma_2 = Z[1/2]^2 x|_(2I, [[2,1],[1,1]]) Z^2` be
Cornulier–Tessera's host, acting persistently on the rooted 10-ary tree as in
the proof. Then:
1. `V_10(Gamma_2)` is finitely presented.
2. `S = [V_10(Gamma_2), V_10(Gamma_2)]` is simple and of finite index, hence
   finitely presented and quasi-isometric to `V_10(Gamma_2)`.
3. `n^2 ≃ δ_(Gamma_2) ≼ δ_S`.
4. `Gamma_2`, and in particular `BS(1,2)`, embeds in `S`.

**What this does and does not settle.** `S` is a concrete finitely presented
simple group containing `BS(1,2)` whose host has quadratic Dehn function. Zaremsky
gives only the lower bound `δ_(Gamma_2) ≼ δ_(V_10(Gamma_2))`. No upper bound on
`δ_S` is known, so this does not settle
`bs12-embeds-in-fp-simple-group-with-polynomial-dehn-function`. It reduces that
test case to two upper bounds, recorded in
`bs12-poly-dehn-simple-host-via-rn-upper-bound`.
