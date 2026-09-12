---
rg: 2
id: weak-invariants-bound-bernoulli-rokhlin-entropy-below
kind: claim
title: A weak-equivalence invariant such as cost bounds the Rokhlin entropy of every nontrivial Bernoulli shift below by a positive number
refuted_by:
  - weak-invariants-give-no-bernoulli-rokhlin-lower-bound
distinct_from:
  every-group-has-positive-rokhlin-entropy-action: that is the positive-entropy existence statement; this is one proposed mechanism for it, a base-independent lower bound through cost, l2-Betti numbers or another weak-equivalence invariant, and it is refuted.
artifacts:
  - research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md
---

**REFUTED.** Proposed mechanism for `every-group-has-positive-rokhlin-entropy-action`. For every
countably infinite group `G` there are a quantity `Φ`, constant on weak-equivalence classes of free
actions (cost, fixed price, approximate finite statistics) or depending on `G` alone (ℓ²-Betti
numbers), and a function `F_G`, such that for every nontrivial finite-alphabet Bernoulli shift
`h^Rok_G(k^G, λ^G) ≥ F_G(Φ(k^G, λ^G)) > 0`.

## Attempts

- **Dies at small bases (2026-09-12, gk-p-inf-cost).** Nontrivial Bernoulli shifts are weakly
  equivalent, so `Φ` is constant on them. But their Rokhlin entropy is at most `H(1−p, p) → 0`.
  Refuted for every group by `weak-invariants-give-no-bernoulli-rokhlin-lower-bound`, already over
  `F_2`, where every free action has cost `2`.
- **What the refutation leaves open.** A lower bound for the group invariant `h_sup(G)` itself,
  which by Seward's Theorem 1.10 is what a Bernoulli lower bound must be. On Kazhdan hosts the
  first-order candidates (infimal cost minus one, `β^(2)_1`) are `0` (artifact Remark 4.2). The
  maximal cost of a Kazhdan group (the open fixed-price question) and the higher ℓ²-Betti numbers
  have no known relation to `h_sup`.
