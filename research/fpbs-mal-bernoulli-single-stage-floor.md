---
rg: 2
id: fpbs-mal-bernoulli-single-stage-floor
kind: claim
title: The Bernoulli shift of Gamma_mal has positive relative cost over the orbit relation of one free stage
distinct_from:
  fpbs-locally-free-free-actions-have-finite-cost: that is the statement that every free action has finite cost; this is a single-stage lower bound for one action, and it refutes that claim.
  fpbs-malnormal-coset-cycles-linear-perimeter: that gives a positive floor for packing certificates only; this asks for a positive floor over all graphings.
  fpbs-mal-long-generator-packing-growth: that would imply the negation of this claim for the Bernoulli shift.
artifacts:
  - research/artifacts/fpbs-shifted-stage-relative-cost-zero-or-infinite-2026-09-17.md
---

**OPEN.** Let `beta` be the Bernoulli shift of
`Gamma_mal = <a, b_1, b_2, ... | b_k = b_{k+1} a b_{k+1}^{-2}>`, and let
`H_1 = <a, b_1>`, which is free of rank 2. Prove that

```text
relC( E_beta ; E_{beta|H_1} ) > 0.
```

**Equivalent forms.** By [[fpbs-shifted-stage-relative-cost-zero-or-infinite]]
the following are equivalent:
- this claim;
- `C(beta) = infinity`;
- `relC(E_beta; E_{beta|H_n}) = infinity` for all `n`.

The negation is `C(beta) = 2`.

**If it holds.**
- `(E_{beta|H_n})_n` is an increasing sequence of cost-2 relations whose union
  has infinite cost. That answers Gaboriau's Q 2.66 positively.
- It answers the second part of Q 2.65, since
  `C - 1 = infinity > beta_1^(2)(Gamma_mal) = 1`.
- It refutes `fpbs-locally-free-free-actions-have-finite-cost`.
- By Tucker-Drob Cor 6.8(2), `E_beta` is not treeable.

**If it fails.** The Bernoulli shift of `Gamma_mal` has cost 2. Any graphing
certificate must use labels outside every fixed stage, with mass tending to 0.

**Known not to prove it.**
- No `l2` or first-Betti bound. All stages and the union have
  `beta_1^(2) = 1`.
- No packing floor. `fpbs-malnormal-coset-cycles-linear-perimeter` bounds
  only packing certificates.
- No zero-cost absorption argument. `fpbs-malnormal-measured-absorption-cap`
  shows that zero-cost absorption cannot leave a stage. That is compatible
  with relative cost 0, which is an infimum that is never attained.

## Attempts

**Homological and packing floors (September 17, 2026, swarm-0917-w5-pull-fp-2).**
- **Linnell ranks.** A relative `D`-rank floor for `(Gamma_mal, H_1)` would
  give a positive floor. It dies at the stage map
  `H_1(H_n, D) -> H_1(H_{n+1}, D)`. That map is an isomorphism, because the
  Fox derivative of `b_{n+1} a b_{n+1}^{-2}` in `b_{n+1}` is nonzero, hence
  invertible in `D`. So the relative invariant is `0`.
- **Packing certificates.** Their floor `delta_mal` bounds only the
  certificate, not `relC`.
- **What a proof would need.** Something that sees label length: the
  unbounded labels a small-mass generating graphing must carry.

**Sprinkle then absorb, attacked from the relC = 0 side (September 17–18,
2026, swarm-0917-w7-w7-fp-last1, host-geometry).**
- **Shape tested.** A cheap proof of the negation: pay a sparse block-factor
  sprinkle `Theta_B` of `b_2` over `E_{H_1}`, at mass `epsilon`, then absorb
  for free by infinite-contact steps. This is the one shape that
  `fpbs-malnormal-measured-absorption-cap` lists as not excluded.
- **Where it dies.** At the first absorption step. By
  [[fpbs-mal-sprinkle-then-absorb-inert]] (route
  `fpbs-mal-sprinkle-then-absorb-inert-proof`, artifact
  `research/artifacts/fpbs-mal-sprinkle-then-absorb-inert-2026-09-17.md`):
  - If `epsilon^{1/|W|^2} < 1/A`, the cluster graph of `E_{H_1} v Theta_B` is
    a.s. fine. This follows from `M(k) <= A^k` of
    [[fpbs-malnormal-coset-cycles-linear-perimeter]].
  - Hence every infinite-contact step with a bounded number of closed-edge
    crossings adds nothing.
  - Labels outside `H_2` are excluded by the cap's Theorem A.
  - If `epsilon^{1/|W|^2} <= 1/(4 A^2)`, the resulting relation misses
    `(x, b_2 x)` on mass `> 1/2`.
- **Invariant.** Almost-sure Bowditch fineness of the cluster graph.
- **What survives.**
  - kappa-escaping contact classes, where the crossing count tends to
    infinity along the class;
  - growing windows;
  - long-generator payments, with constants unbounded in `m`;
  - countably many payments;
  - certificates not built as chains.
- **Next decomposition that can fail.** Show that no `phi` has a non-null set
  of kappa-escaping infinite contact classes joining distinct clusters of a
  sparse block sprinkle. This does not decide the claim, which stays OPEN.

**Sofic sparsity floor for fold seeds (September 18, 2026,
swarm-0917-w8-w8-fp-break, finite-models).**
- **Result.** [[fpbs-weakly-bernoulli-fold-seeds-have-density-floor]]
  (route `fpbs-weakly-bernoulli-fold-seeds-have-density-floor-proof`,
  artifact
  `research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md`).
  For every action of `F(a, b)` weakly contained in Bernoulli, `σ_b ≥ 1/80`.
  So `σ_b(Bernoulli) ∈ [1/80, 5/32]`. The fold artifact had recorded that no
  positive lower bound was known for any free action.
- **Invariant.** Small-set slot sparsity of random Schreier graphs of `F_2`
  at the crossing size `α n`. With high probability, no `m`-set spans
  `(1+η) m` slots when `H(α) + 2αH((1+η)/2) + (1+η)α ln α < 0`. Every
  closure from `S` that crosses size `m` produces `2(m − |S|)` slots.
  Weak containment and the local structure of random permutation models carry
  this to all of `W_b`.
- **What it kills (with Theorem 1.2 of the fold artifact).** On `W_b`, every
  graphing with labels in one double coset `K b^{±1} K` has mass `≥ 1/80`
  at each stage `H_n ≤ H_{n+1}`, uniformly in `n`. So every stagewise
  telescoping scheme `E_{H_n} ∨ b_{n+1}|_{A_n} = E_{H_{n+1}}` has infinite
  total mass. This covers iid, block and factor-of-iid seeds. The odometer
  mechanism of `fpbs-mal-odometer-product-actions-have-cost-two` therefore
  cannot be transported to the Bernoulli shift, and `σ_b` separates the
  odometer products (`0`) from `W_b` (`≥ 1/80`).
- **What survives.**
  - graphings that mix several double cosets `K g K`;
  - labels from deeper stages `b_{n+2}, …`;
  - graphings that do not factor stagewise.
- **Next decomposition that can fail.** A finite-model reduction. Prove that
  the local relative combinatorial cost of random Schreier graphs of `L` over
  the `K`-components is bounded below uniformly in the witness length `T`.
  The cost is taken with extra edges of word length `≤ T`. Lemmas 1 to 3 of
  the artifact transfer any such bound to `W_b`. The missing count is the
  multi-coset analogue of slot sparsity. The claim stays OPEN.
