---
rg: 2
id: distribution-certificates-are-shannon-monotone
kind: claim
title: Over every countably infinite group, a sound distribution-level certificate for Bernoulli generating partitions is a non-decreasing function of Shannon entropy, and a non-constant one already forces positive Rokhlin entropy
distinct_from:
  cluster-entropy-lower-bounds-need-nonpositive-total-weight: that kills cluster functionals of the joint window statistics of a partition; this kills every functional of the one-site distribution alone, with no restriction on its form, using Bowen and Seward realisations instead of product-with-finite-set tests.
  hs-commutative-microstate-bernoulli-entropy-is-base-blind: that concerns the volume of Hilbert--Schmidt commuting-projection microstates, which it finds infinite; this kills the leading-order dimension 1 - sum q_i^2 of that space, and every other non-Shannon distribution functional, as a lower-bound certificate.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that kills quantities constant on weak-equivalence classes, which are base-independent; this kills base-dependent functionals of the generator's distribution.
  entropy-profile-proofs-of-bernoulli-maximality-relativize: that shows proofs through entropy profiles relativize; this is an unconditional statement that the admissible distribution functionals are exactly Shannon-monotone ones.
  every-group-has-positive-rokhlin-entropy-action: that is the open existence statement; this shows that a non-constant sound distribution certificate over G would already imply it for G, so such certificates are no easier than the goal.
artifacts:
  - experiments/distribution-certificates-2026-09-17/level_set_witnesses.py
  - experiments/distribution-certificates-2026-09-17/level_set_witnesses.out
---

**ESTABLISHED** by [[distribution-certificates-are-shannon-monotone-proof]].

**Setting.** Let `G` be countably infinite. Let `P` be the set of finite probability vectors with at least two
nonzero entries, up to permutation, and `P3 ⊂ P` those with at least three. For `p ∈ P`, `B(p)` is the Bernoulli
shift `G ↷ (k^G, p^G)`. A **distribution certificate over `G`** is a map `f : P → [-∞, +∞]` that is **sound**,
meaning that for every `p ∈ P` and every finite generating partition `α` of `B(p)`,
`f(dist α) ≥ f(p)`.

**Theorem.** Let `f` be sound over `G`.

1. If `p, q ∈ P` and `H(q) > H(p)`, then `f(q) ≥ f(p)`.
2. If `p, q ∈ P3` and `H(q) = H(p)`, then `f(q) = f(p)`.
3. If `f(p) > f(q)` for some `p, q ∈ P`, then `H(q) < H(p)` and `h^Rok_G(B(p)) ≥ H(q) > 0`.

So on `P3`, `f = φ ∘ H` with `φ` non-decreasing. A non-constant sound certificate proves POS for `G`, and
it certifies nothing beyond a Rokhlin lower bound that its own soundness already contains.

**Corollary (the class that dies).** None of the following is sound over any countably infinite group:

- the Hilbert--Schmidt commuting-projection dimension `1 - Σ q_i^2`, the leading coefficient of
  `dim U(n)/(U(q_1 n) × ... )`;
- Rényi entropy `H_α` for every `α ∈ [0, ∞]` with `α ≠ 1`, including the support count `log |supp q|` and the
  min-entropy `-log max q_i`;
- Tsallis entropy `S_α` for every `α ≠ 1`;
- any strictly increasing function of these.

The invariant is the one-site distribution of the generating partition. Every member dies at one of two
realisation steps:

- Bowen's almost-Ornstein isomorphism
  ([[bowen-every-countably-infinite-group-is-almost-ornstein]]) makes each Shannon level set in `P3` occur as
  the distributions of generators of a single shift;
- Seward's prescribed-distribution generator theorem ([[seward-small-support-relative-generators]]) makes every
  distribution of larger Shannon entropy occur.

Explicit witnesses are in `experiments/distribution-certificates-2026-09-17/level_set_witnesses.out`.

- Base `q = (a, a, 1-2a)` with `a ≈ 0.4100324`, so that `H(q) = 1.5` bits. It has a generating partition of
  distribution `(1/2, 1/4, 1/4)`, whose value `1 - Σ^2 = 0.625` is below the base's `0.6314`.
- Base `(1/3, 1/3, 1/3)`, with `H = 1.585` bits. It has a generating partition of distribution
  `(3/5, 1/10, 1/10, 1/10, 1/10)`, with `H = 1.771` bits and `1 - Σ^2 = 0.6 < 2/3`.

**Consequence for the positive-entropy programme.** Any proof of POS, INF or RBS that bounds the entropy
of a generator through a statistic of its distribution must use Shannon entropy itself, up to a monotone
reparametrisation. Such a proof must also establish that statistic's soundness, and by part 3 that is at
least as strong as the conclusion. Collision, rank, dimension and support counts are excluded on every group,
amenable or not, including a hypothetical group of zero Rokhlin supremum. On such a group every sound
certificate is constant on `P`, by part 1 together with Seward.

What survives:

- statistics of **joint** window distributions, which are handled by
  [[cluster-entropy-lower-bounds-need-nonpositive-total-weight]] and
  [[minimal-window-shannon-derivations-miss-rokhlin-domination]];
- multinomial (diagonal, sofic-type) counts, whose exponent is Shannon entropy.
