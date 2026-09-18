---
rg: 2
id: distribution-certificates-are-shannon-monotone-proof
kind: route
title: Seward realises every distribution of larger entropy and Bowen every distribution of equal entropy as a generator of one Bernoulli shift
target: distribution-certificates-are-shannon-monotone
requires:
  - seward-small-support-relative-generators
  - bowen-every-countably-infinite-group-is-almost-ornstein
artifacts:
  - experiments/distribution-certificates-2026-09-17/level_set_witnesses.py
  - experiments/distribution-certificates-2026-09-17/level_set_witnesses.out
---

Fix a countably infinite `G` and a sound `f`. For `p ∈ P` the shift `B(p)` is ergodic (indeed mixing) and its
space `(k^G, p^G)` is non-atomic, because `G` is infinite and `p` has two nonzero entries.

**Step 0 (upper bound).** The time-zero partition generates `B(p)`, so `h^Rok_G(B(p)) ≤ H(p)`.

**Step 1 (Seward realisation).** Let `q ∈ P` with `h^Rok_G(B(p)) < H(q)`. Apply
[[seward-small-support-relative-generators]] with `r = 1`, `F` trivial and `p̄ = q`. This gives a Borel
pre-partition `α = {A_i}` with `µ(∪α) = 1`, `µ(A_i) = q_i`, and `σ-alg^red_G(α) = B(X)`. Add the null set
`X \ ∪α` to `A_0` to get a partition `β` with `β ⊒ α`. Lemma 2.2 of the same import gives
`σ-alg_G(β) ⊇ σ-alg^red_G(α) = B(X)`, so `β` is a finite generating partition of `B(p)` with `dist β = q`.
Soundness gives `f(q) ≥ f(p)`.

**Part 1.** If `H(q) > H(p)`, then Step 0 gives `h^Rok(B(p)) ≤ H(p) < H(q)`, and Step 1 applies.

**Part 2.** Let `p, q ∈ P3` with `H(q) = H(p)`. A finite vector with at least three nonzero entries is
not a two-atom space. By [[bowen-every-countably-infinite-group-is-almost-ornstein]] there is a measure
conjugacy `Φ : B(q) → B(p)`. The image under `Φ` of the time-zero partition of `B(q)` generates `B(p)` and has
distribution `q`, so `f(q) ≥ f(p)`. Exchanging `p` and `q` gives equality.

**Part 3.** Suppose `f(p) > f(q)`. By Part 1, `H(q) ≤ H(p)`. Now suppose `h^Rok(B(p)) < H(q)`. Then Step 1
gives `f(q) ≥ f(p)`, a contradiction. So `h^Rok(B(p)) ≥ H(q)`, and `H(q) > 0` because `q` has two nonzero
entries. In particular `H(q) ≤ h^Rok(B(p)) ≤ H(p)`.

**Corollary.** It suffices to exhibit, for each listed functional `g`, vectors in `P` with `H(q) > H(p)` and
`g(q) < g(p)`. Part 1 then fails.

- **Collision / HS dimension `1 - Σ q^2`.** Take `p = (1/3, 1/3, 1/3)` and `q = (3/5, 1/10^4)`, meaning four
  entries of `1/10`. Then `H(p) = ln 3 < 0.6 ln(5/3) + 0.4 ln 10 = H(q)`, since `1.0986 < 1.2275`, while
  `1 - Σq^2 = 3/5 < 2/3 = 1 - Σp^2`. The equal-entropy witness for Part 2 is in the artifact.
- **Rényi `α > 1`, including `α = ∞`.** Take `p = (1/3, 1/3, 1/3)`. Let `q` have one entry `1 - δ` and `k`
  entries `δ/k`. Then `H_α(q) ≤ (α/(α-1)) H_∞(q) = (α/(α-1)) ln(1/(1-δ))`, which is below `ln 3` for small `δ`,
  while `H(q) ≥ δ ln(k/δ) > ln 3` for `k` large.
- **Rényi `α ∈ [0, 1)`.** Take `q = (1/3, 1/3, 1/3)`, so `H_α(q) = ln 3`. Let `p` have one entry `1 - δ` and `k`
  entries `δ/k`, with `k = ⌈e^{1/(2δ)}⌉`. Then `H(p) ≤ h(δ) + δ ln k`, which tends to `1/2 < ln 3` as `δ → 0`.
  Also `H_α(p) ≥ (1/(1-α)) ln(k (δ/k)^α) = ln k - (α/(1-α)) ln(1/δ)`, which tends to `∞` as `δ → 0`. So for
  small `δ`, `H(q) > H(p)` but `H_α(q) < H_α(p)`.
- **Tsallis `S_α` and monotone transforms.** `S_α = (1 - e^{(1-α)H_α})/(α - 1)` is a strictly increasing
  function of `H_α`, so the same witnesses apply.
