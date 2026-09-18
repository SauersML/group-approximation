---
rg: 2
id: fpbs-mal-odometer-product-actions-have-cost-two
kind: claim
title: Every free action of Gamma_mal times the profinite odometer of an integer character has cost 2, so Gamma_mal has infimal cost 2
distinct_from:
  fpbs-locally-free-free-action-costs-are-c-star-or-infinite: that is the dichotomy C in {c*, infinity}, with the value c* conditional on some free action having finite cost; this exhibits such an action for Gamma_mal, so C(Gamma_mal) = 2 unconditionally.
  fpbs-locally-free-free-actions-have-finite-cost: that is the open statement that every free action has finite cost; this proves finite cost only for actions with a chi-odometer factor, and leaves the Bernoulli shift open.
  fpbs-mal-bernoulli-single-stage-floor: that conjectures a positive stage floor for the Bernoulli shift; this proves the stage relative cost is 0 for odometer products, so that floor, if true, makes Gamma_mal a fixed-price counterexample.
  fpbs-shifted-stage-relative-cost-zero-or-infinite: that is the 0-or-infinity dichotomy for shift-invariant actions; this computes the value 0 for a class of actions that need not be shift-invariant, by an explicit seed set.
  fpbs-mal-stage-block-sprinkling-threshold: that is a first-moment obstruction for iid or block sprinkles in the Bernoulli shift; this uses sprinkles measurable for a compact abelian factor, which that obstruction does not cover.
  fpbs-extension-routes-to-finite-cost-are-circular: that kills descent of finiteness along factor maps and assumes C(Gamma) finite; this proves C(Gamma_mal) finite, which is the hypothesis there, and uses no descent.
  fpbs-relative-fixed-price-free-pairs: that is the open inequality relC <= rank difference for every free action of a free pair; this proves relC = 0 at the pair (F_2, <a, bab^-2>) for every free action with a chi-odometer factor.
artifacts:
  - research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md
  - experiments/fpbs-fold-bootstrap-2026-09-17/odometer_threshold.py
  - experiments/fpbs-fold-bootstrap-2026-09-17/odometer_threshold_out.txt
  - experiments/fpbs-fold-bootstrap-2026-09-17/certify.py
  - experiments/fpbs-fold-bootstrap-2026-09-17/certify_out.txt
---

**ESTABLISHED** through `fpbs-mal-odometer-product-actions-have-cost-two-proof`.

Let `Gamma_mal = <a, b_1, b_2, ... | b_n = b_{n+1} a b_{n+1}^{-2}>` and
`H_n = <a, b_n>`, which is free of rank 2. Define the character
`χ : Gamma_mal → Z` by:
- `χ(a) = 1`;
- `χ(b_n) = −1` for odd `n`;
- `χ(b_n) = 2` for even `n`.

Let `β` be any free p.m.p. action of `Gamma_mal`, and let `β × Ẑ_χ` be the
product action `g(x, z) = (g x, z + χ(g))` on `X × Ẑ`. Then:

1. `relC( E_{H_{n+1}} ; E_{H_n} ) = 0` on `β × Ẑ_χ` for every `n`. Explicitly,
   `E_{H_n} ∨ b_{n+1}|_{A_N} = E_{H_{n+1}}` with
   `A_N = { z mod N ∈ {0, 1, 2} }`, which has measure `3/N`.
2. `C(β × Ẑ_χ) = 2`.
3. Hence `C(Gamma_mal) = 2`, which is `c* = 1 + β_1^(2)(Gamma_mal)`. Every
   free action of `Gamma_mal` has pseudocost exactly `2`, and `Gamma_mal` has
   fixed price iff every free action has finite cost.

**Mechanism.** For the free pair `K = <a, b a b^{-2}> ≤ L = <a, b>`,
`R_K ∨ b|_A = R_L` iff the 2-of-3 closure of `A` on the triples
`{w, a w, b w}` is conull. That is Lemma 1.1 plus Theorem 1.2 of the artifact;
only Lemma 1.1 is used here. On the odometer coordinate, the triples are
`{q, q+1, q+t}` with `t = χ(b) ∈ {−1, 2}`. Three consecutive residues then
fill `Z/N` by induction.

**Consequences.**
- `fpbs-mal-bernoulli-single-stage-floor`, if true, now makes `Gamma_mal` a
  counterexample to fixed price (Bernoulli cost `∞` against cost `2` here).
- `fpbs-relative-fixed-price-free-pairs` holds at the pair
  `(F_2, <a, bab^{-2}>)` for every free action with a factor
  `z ↦ z + χ(g)` on `Ẑ`, `χ(a) = 1`.
- The Bernoulli shift is mixing, hence has no compact factor, and remains open.

Artifact: `research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md`, §1–§2.
A web search found no earlier statement that `Gamma_mal` has finite infimal
cost. The argument is elementary, so it is recorded as new relative to the
graph rather than to the literature.
