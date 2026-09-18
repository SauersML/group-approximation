---
rg: 2
id: fpbs-bernoulli-fold-seeds-have-density-at-least-2-25-proof
kind: route
title: Transfer the fold closure to random permutation models and count full triples of half-size sets at the crossing
target: fpbs-bernoulli-fold-seeds-have-density-at-least-2-25
requires: []
artifacts:
  - research/artifacts/fpbs-full-triple-fold-seed-floor-2026-09-17.md
  - research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md
  - experiments/fpbs-full-triple-floor-2026-09-17/full_triple_constant.py
  - experiments/fpbs-full-triple-floor-2026-09-17/full_triple_constant_out.txt
---

The complete proof is §1–§2 of
`research/artifacts/fpbs-full-triple-fold-seed-floor-2026-09-17.md`.

Three transfer lemmas are taken verbatim, with their proofs, from §1 of
`research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md`:
Lemma 1 (weak containment moves patterns), Lemma 2 (cylinder approximation)
and Lemma 3 (random permutation models). They use only two outside facts:
Kechris' definition of weak containment, and the bounds
`e^{N H(K/N)}/(N+1) ≤ C(N, K) ≤ e^{N H(K/N)}`.

1. **Transfer.** Lemmas 1–3 give the following. Suppose some `A` has conull
   closure and `μ(A) < c − 4γ`. Then there are finite-model sets `S_n` with
   `E|S_n|/n → ρ(B′) < μ(A) + 2γ` and
   `P(|cl(S_n)| ≥ n/2) ≥ 1 − 6γ − o(1)`.
2. **Crossing (Lemma 5′).** If `|S| < m ≤ |cl(S)|`, then the sequential
   closure passes through an `m`-set `I`. At least `m − |S|` distinct
   indices `v` of `I` are full triples of `I`, meaning `v`, `σ_a v` and
   `σ_b v` all lie in `I`. These are the firing indices, and each fires at
   most once.
3. **First moment (Lemma 4′).** For `|I| = m` and `V ⊆ I` with `|V| = f`,
   `P(σ_a V ⊆ I, σ_b V ⊆ I) = [C(m,f)/C(n,f)]^2`. With high probability, no
   `⌈n/2⌉`-set has `⌈21 n/50⌉` full triples. The bound is
   `C(n,m) C(m,f)^3 / C(n,f)^2`, and it has exponent `n J(1/2, 21/50)`,
   where `J(1/2, 21/50) = −0.00793`. This value is checked in 40-digit
   arithmetic in `full_triple_constant.py`. The exact finite-`n` logarithm
   is `−87.0` at `n = 10^4`.
4. **Combine.** On the intersection of these events, `|S_n| > n/2 − 21n/50 − 1`.
   Taking expectations and letting `n → ∞`, then `γ → 0`, gives
   `μ(A) ≥ 2/25`. The error term works because `2 + 3c/(1−x) = 62/25 < 4`.
