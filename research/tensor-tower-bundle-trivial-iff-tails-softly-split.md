---
rg: 2
id: tensor-tower-bundle-trivial-iff-tails-softly-split
kind: claim
title: A fibred tensor tower gives a trivial hyperfinite W*-bundle iff its tail bundles admit soft half splittings
distinct_from:
  r-fibre-bundle-triviality-iff-uniform-central-halving: that is Ozawa's criterion inside an abstract bundle; this translates it, for fibred tensor towers, into a pointwise topological condition on the tail vector bundles.
  block-balanced-towers-have-central-halving: that gives central halving from equal-rank block splittings; this characterizes central halving for tensor towers whose multiplicity bundles need not split at all.
  nontrivial-w-star-bundle-with-r-fibres-exists: that is the existence question; this reduces its tensor-tower case to a question about vector bundles.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-part2-2026-09-12.md
---

Let `W_k → Y_k` be complex vector bundles of rank `w_k ≥ 2` over compact metrizable
spaces. Put `Z_m = Π_{k≤m} Y_k` and `U_{n,m} = ⊠_{n<k≤m} W_k`, pulled back to `Z_m`. Let
`A = lim C(Z_m, End(U_{0,m}))` with maps `a ↦ a ⊗ 1`. Then:
- `T(A) = Prob(X̂)` is Bauer, with `X̂ = Π_k Y_k`;
- the strict closure `M` is a W*-bundle over `X̂` with fibres `R`.

**Criterion.** `M ≅ C_σ(X̂, R)` if and only if, for every `n` and `ε > 0`, some `m > n`
admits a positive contraction `h ∈ C(Z_m, End(U_{n,m}))` with

```text
tr(h(z) − h(z)²) ≤ ε   and   |tr h(z) − 1/2| ≤ ε   for every z ∈ Z_m
```

(normalized fibre trace). Call `h` an `ε`-soft half splitting of the tail.

**Consequences.**
- Split multiplicity bundles, such as `W_k = θ ⊕ L_k`, give exact splittings, hence
  trivial bundles.
- If `dim Π_{n<k≤m} Y_k ≤ rank U_{n,m}` for some `m`, general position gives an exact
  splitting.
- So a witness from a tensor tower needs indecomposable multiplicity bundles and tail
  dimension exceeding tail rank at every depth. That is the quadratic-growth regime
  where Toms's Thom–Porteous obstructions survive 2-norm approximation.
- Its negation, at one `n` and `ε`, answers BBSTWW Question 3.14
  (`some-tensor-tower-has-unsplittable-tails`).
