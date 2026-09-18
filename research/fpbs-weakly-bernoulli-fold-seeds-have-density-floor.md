---
rg: 2
id: fpbs-weakly-bernoulli-fold-seeds-have-density-floor
kind: claim
title: In every action of F(a,b) weakly contained in Bernoulli, a set whose 2-of-3 fold closure on the triples {w, aw, bw} is conull has measure at least 1/80
distinct_from:
  fpbs-mal-bernoulli-single-stage-floor: that asks for a positive floor on relC over all graphings; this bounds only the one-double-coset quantity sigma_b, and multi-double-coset graphings stay open there.
  fpbs-mal-odometer-product-actions-have-cost-two: that proves sigma_b = 0 on chi-odometer products; this proves sigma_b >= 1/80 on the weak-containment class of Bernoulli, which those products are not in.
  fpbs-mal-stage-block-sprinkling-threshold: that is a first-moment obstruction for iid or block sprinkles of the Bernoulli shift; this covers every measurable seed set in every action weakly contained in Bernoulli, including all factor-of-iid seeds.
  fpbs-mal-sprinkle-then-absorb-inert: that kills one sprinkle-then-absorb mechanism; this is a lower bound on the fold seed density itself, proved through random Schreier graph sparsity.
artifacts:
  - research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md
  - experiments/fpbs-fold-seed-floor-2026-09-17/floor_constant.py
  - experiments/fpbs-fold-seed-floor-2026-09-17/floor_constant_out.txt
  - experiments/fpbs-fold-seed-floor-2026-09-17/random_schreier_contagious.py
  - experiments/fpbs-fold-seed-floor-2026-09-17/random_schreier_contagious_out.txt
---

**ESTABLISHED** through `fpbs-weakly-bernoulli-fold-seeds-have-density-floor-proof`.

Let `L = F(a, b)` act p.m.p. on `(X, μ)`. For measurable `A ⊆ X` let `cl(A)`
be the closure of `A` under the rule "if two of the three entries of
`T_w = (w, a w, b w)` (with multiplicity) are in the set, add the third".
Put `σ_b(X) = inf { μ(A) : cl(A) conull }`.

**Claim.** If `L ↷ X` is weakly contained in a Bernoulli shift of `L`, then
`σ_b(X) ≥ 1/80`. More precisely, `σ_b(X) ≥ (1−η) α / 2` whenever

```text
H(α) + 2α H((1+η)/2) + (1+η) α ln α < 0,
```

and the best such constant is about `0.01406`.

**Reading.** This is the stage pair `K = ⟨a, b a b^{-2}⟩ ≤ L`, and it
applies at every stage `H_n ≤ H_{n+1}` of `Gamma_mal`, for every action of
`Gamma_mal` weakly contained in its Bernoulli shift (restriction of a
Bernoulli shift to `H_{n+1}` is a Bernoulli shift). With Theorem 1.2 of
`research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md` (exactness,
not part of this claim), it gives:
- `relC_{K b^{±1} K}(R_L; R_K) ≥ 1/80` on this class;
- the stagewise telescoping scheme `E_{H_n} ∨ b_{n+1}|_{A_n} = E_{H_{n+1}}`
  has total mass `∞` there.

Together with `σ_b ≤ 5/32` from that artifact, `σ_b(Bernoulli) ∈ [1/80, 5/32]`.
Graphings that use several double cosets, or deeper-stage labels, are not
covered.
