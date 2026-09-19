---
rg: 2
id: fpbs-bernoulli-fold-seeds-have-density-at-least-2-25
kind: claim
title: In every action of F(a,b) weakly contained in Bernoulli, a set whose 2-of-3 fold closure on the triples {w, aw, bw} is conull has measure at least 2/25
distinct_from:
  fpbs-weakly-bernoulli-fold-seeds-have-density-floor: that proves the floor 1/80 (optimum 0.01406) by counting slots of small sets at crossing size n/8; this proves 2/25 (optimum 0.0819) by counting full triples, whose two slots sit at one index, at crossing size n/2, and it narrows the Bernoulli window to [2/25, 5/32].
  fpbs-mal-bernoulli-single-stage-floor: that asks for a positive floor on relC over all graphings; this bounds only the one-double-coset quantity sigma_b, and multi-double-coset and deep-label graphings stay open there.
  fpbs-mal-graphing-b-length-weighted-floor: that is the b-length-weighted floor for all double cosets, proved from any floor on sigma_b; this is a better floor on sigma_b itself, which that result then inherits as 2/25.
  fpbs-mal-stage-block-sprinkling-threshold: that is a first-moment obstruction for iid or block sprinkles of the Bernoulli shift; this covers every measurable seed set in every action weakly contained in Bernoulli.
artifacts:
  - research/artifacts/fpbs-full-triple-fold-seed-floor-2026-09-17.md
  - research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md
  - experiments/fpbs-full-triple-floor-2026-09-17/full_triple_constant.py
  - experiments/fpbs-full-triple-floor-2026-09-17/full_triple_constant_out.txt
  - experiments/fpbs-full-triple-floor-2026-09-17/full_triple_crossing.py
  - experiments/fpbs-full-triple-floor-2026-09-17/full_triple_crossing_out.txt
---

**ESTABLISHED** through `fpbs-bernoulli-fold-seeds-have-density-at-least-2-25-proof`.

Let `L = F(a, b)` act p.m.p. on `(X, μ)`. For measurable `A ⊆ X`, let
`cl(A)` be the closure of `A` under the following rule on the triples
`T_w = (w, a w, b w)`, counted with multiplicity: if two of the three
entries are in the set, add the third. Put
`σ_b(X) = inf { μ(A) : cl(A) conull }`.

**Claim.** If `L ↷ X` is weakly contained in a Bernoulli shift of `L`, then
`σ_b(X) ≥ 2/25`. More precisely, `σ_b(X) ≥ x − z` whenever

```text
J(x, z) = H(x) + 3 x H(z/x) − 2 H(z) < 0,
```

and `J(1/2, 21/50) = −0.00793… < 0`. The best constant this gives is about
`0.0819`.

**Reading.** Together with the iid upper bound `5/32` of
`research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md`, this gives
`σ_b(Bernoulli of F_2) ∈ [2/25, 5/32]`. The previous window was
`[1/80, 5/32]`.

The claim applies at every stage `H_n ≤ H_{n+1}` of `Gamma_mal`, for every
action in `W_b(Gamma_mal)`. The restriction argument is that of
`fpbs-weakly-bernoulli-fold-seeds-have-density-floor`.

Every consequence in the cone that is stated as `≥ 1/80` via `σ_b` improves
to `≥ 2/25`, with the same proof. For example, the `b`-length-weighted floor
becomes `Σ |h| μ(D_h) ≥ 2/25`.

**Scope.** This is not a decision of `fpbs-mal-bernoulli-single-stage-floor`.
The following stay open:

- multi-double-coset graphings with long, shared chords (P2);
- deep-label promotions (D1).

The first-moment method used here cannot give more than `≈ 0.0822`. Greedy
contagious sets on random Schreier graphs have density `≈ 0.116`.
