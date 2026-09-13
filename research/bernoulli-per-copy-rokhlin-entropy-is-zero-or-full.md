---
rg: 2
id: bernoulli-per-copy-rokhlin-entropy-is-zero-or-full
kind: claim
title: On every countably infinite group the per-copy Rokhlin entropy of amplified Bernoulli shifts is zero or full
distinct_from:
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: that imports Seward's formula min{H(L), h_sup(G)} for one base; this applies it along amplified alphabets and the finitary window value and derives the collapse of every per-copy lower bound.
  self-copy-host-rokhlin-deficits-need-unbounded-windows: that assumes h_sup in {0, infinity} and gets collapse at one copy; this assumes nothing about G and gives collapse per copy, which is its items 2 and 3 on every group.
  rokhlin-window-transport-is-dominated: that asks for the transport bound with constant 1; this shows that any constant already forces constant 1.
artifacts:
  - research/artifacts/rokhlin-supremum-dichotomy-on-leavitt-units-and-v-2026-09-12.md
---

**OPEN** (proved in Section 2 of the artifact; held open until w4-vf-positive-b re-derives it). Let `G` be countably
infinite and `|A| = q >= 2`. For every `k >= 1`,

    h^Rok_G((A^k)^G) = min{ k log q, h^Rok_sup(G) }.

Consequently:

1. `rho_q(G) ∈ {0, log q}`, and `rho_q(G) = log q` iff INF(G).
2. `inf Phi ∈ {0, log q}` (`bernoulli-rokhlin-deficit-has-a-finitary-witness`). A floor `Phi >= c` for one `c > 0` at
   one `q` gives INF(G).
3. One configuration with `Phi < log q` at one `q` gives, at every `q'` and every `eps > 0`, a configuration with
   `Phi < eps`.
4. Transport domination with any constant `C` gives INF(G), and so domination with constant 1. This removes the
   self-copy hypothesis from Corollary 2 of `research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md`.
5. INF(G) iff `sup_k h^Rok_G((A^k)^G) = infinity`. Otherwise the deficit `k log q - h^Rok_G((A^k)^G)` grows
   linearly in `k`.

*Proof.* Item 1 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts` (Theorem 1.10) with base entropy
`k log q < infinity` gives the formula. Divide by `k` and let `k -> infinity`. Theorem 3 of the route artifact gives
`rho_q = inf Phi`. Corollary 2(1) of the random-order artifact gives item 4.

**Scope.** Every lower bound of the form "floor", "linear growth on a subsequence", "reverse restriction with constant
loss from an INF subgroup" or "domination with a constant" is equivalent to INF(G). So there is no intermediate
quantitative target for a nonsofic host (artifact Remark 2.2). It proves no new case of INF.

## Attempts

- **Derivation (w7-rokhlin-dichotomy, 2026-09-12).** Derived in Section 2 of the artifact, from Theorem 1.10 as
  imported and Theorem 3 of `research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md`. No proof route has
  landed yet, pending independent re-derivation by w4-vf-positive-b.
