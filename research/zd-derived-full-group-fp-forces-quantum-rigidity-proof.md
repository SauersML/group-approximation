---
rg: 2
id: zd-derived-full-group-fp-forces-quantum-rigidity-proof
kind: route
title: The group representation of an operator family propagates commutation one step at a time through a two-idempotent certificate
target: zd-derived-full-group-fp-forces-quantum-rigidity
requires:
  - zd-derived-full-group-fp-excludes-periodic-quantum-tilings
  - zd-derived-full-group-fp-forces-finite-type
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - sft-crossed-product-fp-iff-quantum-rigid
artifacts:
  - research/artifacts/labbe-group-fp-forces-quantum-rigidity-2026-09-13.md
  - research/artifacts/labbe-periodic-quantum-tilings-obstruct-fp-2026-09-13.md
  - experiments/labbe-relation-climbing/idealcert.py
---

The full proof is in the first artifact, Sections 1–3. Here are the steps and where each input enters.

1. **The representation.** Let `G = <S | ℛ>` be finitely presented. By the unit map of
   `zd-derived-full-group-fp-excludes-periodic-quantum-tilings` (part 1 artifact, Theorem 1, step 2),
   `G` maps to `A_D^×` for `D >= D_0`. A family (Q1)–(Q3) at scale `D` makes `V = W ⊗ k[Z^2]` an
   `A_D`-module, the construction of `sft-crossed-product-fp-iff-quantum-rigid`. So `rho` is a
   representation of `G` on `V`.
2. **Product form.** Every rule generator acts as `prod_c (1 + E_σ(c) ⊗ (γ_c - 1))`. As long as the
   observables of a ball or domino commute, every ChJN word `W(q, e)` has the same form with coefficient
   `E_q(c)`. This is the operator form of Lemma A in `zd-derived-full-group-fp-forces-finite-type-proof`,
   with core radius `R_1'` (no compatible self-translates at `ℓ_1` offsets `<= 4`). Unintended factors
   are orthogonal through their cores, using only commutation at distance `<= ρ + R_1' + 4`.
3. **Frontier.** Suppose commutation and legality hold up to `ℓ_1`-distance `d`, and let `|u|_1 = d + 1`.
   - Balls (for `d` even) or dominoes (for `d` odd) `Δ_a` and `Δ_b = Δ_a + h` see `u` as their only new
     difference.
   - For compatible legal patterns `p` on `Δ_a` and `p'` on `Δ_b`, put `a = W(p, e)` with `e ⊥ h`, and
     `b = W(p', h)`. Their triples share one site. In `G`, `[a, b]^3 = 1`, and `[a, b']^3 = 1` where
     `b'` is the product over the other compatible patterns.
   - On the image of the core and overlap projections the five-site model is exact, with coefficients
     `P`, `Q` and `1 - Q`.
   - Lemma NC, the exact certificate `idealcert.py`, gives `PQ = QP` when `char k ∉ {3, 5}`.
     Summing over patterns gives commutation at distance `d + 1`.
4. **Legality.** `W(q, e) = 1` in `G` for illegal `q` (Corollary C of the peer route). In product form
   this kills `E_q` on balls and dominoes of diameter `d + 1`.
5. **Conclusion.** By induction all observables commute. So `X` is `D`-rigid for `D >= max(D_0, r)`,
   and `sft-crossed-product-fp-iff-quantum-rigid` makes the crossed product finitely presented.
   (`minimal-z2-subshift-derived-full-groups-are-fg-simple` supplies the generating set `S`.) ∎
