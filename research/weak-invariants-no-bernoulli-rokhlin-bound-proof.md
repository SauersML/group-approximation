---
rg: 2
id: weak-invariants-no-bernoulli-rokhlin-bound-proof
kind: route
title: Weakly equivalent bases with vanishing base entropy force every such bound to be non-positive
target: weak-invariants-give-no-bernoulli-rokhlin-lower-bound
requires:
  - nontrivial-bernoulli-shifts-are-weakly-equivalent
  - cost-is-constant-on-weak-equivalence-classes
artifacts:
  - research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md
---

Section 3 of the artifact.
1. All nontrivial finite-alphabet Bernoulli shifts are weakly equivalent, so `Φ` is constant on
   them. For cost this is by monotonicity; group invariants are constant trivially.
2. The time-zero partition generates, so `h^Rok ≤ H(λ)`.
3. The bases `(1−p, p)` have `H → 0`, so `F(Φ_B) ≤ 0`.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 5.3 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
