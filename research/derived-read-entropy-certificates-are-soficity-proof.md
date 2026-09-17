---
rg: 2
id: derived-read-entropy-certificates-are-soficity-proof
kind: route
title: Fannes-corrected chain-rule count, then unit-incidence pinning turns a tight derived-read model into a reading model
target: derived-read-entropy-certificates-are-soficity
requires: [reading-model-entropy-certificates-are-soficity]
artifacts:
  - research/artifacts/derived-read-count-certificates-force-soficity-2026-09-17.md
---

Sections of the artifact:

- **Section 2 (Lemma A').**
  - Code and site laws are within TV `epsilon` of the Bernoulli laws. Continuity of entropy (Fannes--Audenaert) costs
    `delta/2` per code and `delta` per site.
  - Independence of the good sites gives
    `|V| k log q = H(Z_V) <= sum H(C_u) + sum H(Z_i | C_(sigma_F(i)))`.
- **Section 3 (Lemma P).**
  1. The pair `(g^-1, g)` gives `P(v_(sigma_(g^-1)(i), g) = Z_i) >= 1 - epsilon`, so `sigma_g` is injective on `V` when
     `epsilon < 1/4`.
  2. Read-back maps `tau_e(u)` are the unique preimage site.
  3. At most `b^2(mu-1)|V|` good sites use a non-full code.
  4. Build the reading model `R`, with a sink site `∞` and a sink code `⊥`.
  5. Sites of `V_R` have well-defined injective charts: equal points force `P(Z_j = Z_j') >= 1 - 3 epsilon`, and
     distinct points force `P(read = read') <= 1/2 + epsilon`, with `epsilon < 1/6`.
  6. No other site of `R` is good. For sites outside `V`, `tau_1(sigma_1(i))` is a different good site.
  - Corollary P then applies Lemma B of the required node `reading-model-entropy-certificates-are-soficity` verbatim
    to `R`.
- **Section 4 (Theorem D).**
  - `1 => 3` is the required node's Theorem, because reading models are derived-read models with `epsilon = 0`.
  - `3 => 2` comes from the configuration `psi = x(1)` on `(B_r,B_r)`.
  - `2 => 1` is Corollary P.
  - The obstruction is `mu >= 1 + eta_1` for `epsilon < 1/6`, with `eta_1 = eta_0/(1 + b^2(1+eta_0))`. When
    `1/6 <= epsilon <= 1/2`, the Fannes term already loses `(1/3) log q`.
- **Sections 5 and 6.** The death step, what the class contains and the new gate.

The configuration conventions are those of `bernoulli-rokhlin-deficit-has-a-finitary-witness`, used as definitions,
and `EL_D(R)` is only an example host.
