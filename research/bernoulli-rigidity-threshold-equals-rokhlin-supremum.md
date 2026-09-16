---
rg: 2
id: bernoulli-rigidity-threshold-equals-rokhlin-supremum
kind: claim
title: Over a group with finite Rokhlin supremum, every Bernoulli shift with base entropy above the supremum is isomorphic to one of different base entropy
distinct_from:
  bernoulli-shifts-above-rokhlin-supremum-are-isomorphic: that demands one isomorphism class for all levels above the supremum; this demands only that no level above the supremum is rigid, and is the second of the two halves into which that claim splits.
  eventual-bernoulli-collapse-at-finite-rokhlin-supremum: that asks for total collapse above some unspecified level; this asks for non-rigidity at every level above the supremum, possibly with countable classes.
  zero-rokhlin-supremum-forces-bernoulli-collapse: that asks at supremum zero for some non-rigid level; this asks at every finite supremum that every level above the supremum be non-rigid.
  bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square: that proves some collapse exists iff some own-square exists; this asks for nontrivial isomorphisms whose lower base entropy approaches the supremum.
---

**OPEN.** Let `G` be countably infinite with `s = h^Rok_sup(G) < ∞`. For every `h ∈ (s, ∞)` there is `h' ≠ h`
such that the Bernoulli shifts over `G` with base entropies `h` and `h'` are isomorphic.

**Equivalent forms.**
- The set `R(G)` of non-rigid levels is upward closed and contained in `[s, ∞)`
  (`bernoulli-collapse-is-null-or-eventually-total`, item 3). So the claim says `r(G) = inf R(G) = s`.
- Equivalently, there are nontrivial Bernoulli isomorphisms `X_a ≅ X_b` with `a < b` and `a` arbitrarily close
  to `s`.
- It suffices to check `h` along one sequence decreasing to `s`.

**Consequences.**
- Together with `eventual-bernoulli-collapse-at-finite-rokhlin-supremum`, it gives
  `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`, through route
  `above-supremum-collapse-from-eventual-collapse-and-descent`.
- At `s = 0` it gives `D(G) ≠ {0}`.

**Model tests.**
- Sofic groups have `s = ∞`, so the claim is vacuous there.
- No group with `s < ∞` is known.
- The formal relation "`a ≈ b` iff `a = b` or `a, b ≥ M`", with `M > s`, satisfies translation, transitivity,
  analyticity and Seward's threshold (the formal content of items 1–4 and 6 of
  `bernoulli-isomorphism-collapse-set-is-a-subgroup`), and fails this claim. So no argument using only that calculus can prove it (artifact of
  `bernoulli-collapse-is-null-or-eventually-total`, Section 5).

## Attempts

- **Cancellation from a high collapse (dies at cancellation).**
  - Suppose all `X_h` with `h ≥ M` are isomorphic, and let `s < a < M`. Then
    `X_(M−a) × X_a ≅ X_M ≅ X_(2M) ≅ X_(M−a) × X_(a+M)`.
  - Cancelling the common Bernoulli factor `X_(M−a)` would give `X_a ≅ X_(a+M)`, so `a` would be non-rigid.
  - Cancellation of a Bernoulli factor is known only through an entropy classification of Bernoulli shifts. When
    `s < ∞`, no such classification is available above `s`.
  - Relative Rokhlin entropy of a split Bernoulli factor of base entropy `b` is `min(b, s)` (Proposition 6.5 of
    arXiv:1501.03367, as used on `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`). It is `s` for both
    candidate factors, so it gives no lever.
- **Rescaling through other groups (dies because thresholds never drop).**
  - Co-induction to an overgroup keeps every witness level, and the supremum can only fall
    (`bernoulli-entropy-counterexample-constraints`, item (d)).
  - Restriction to an index-`k` subgroup multiplies witnesses by `k`
    (`bernoulli-isomorphism-collapse-set-is-a-subgroup`, item 7). Whether the supremum scales by `k` is Seward's
    open finite-index formula (`seward-direct-product-relative-rokhlin-entropy-conjecture`).
  - In no case does a witness move closer to the supremum of the new group by a known amount.
- **Approximate isomorphisms (dies at exactness).**
  - Seward's Theorem 10.1 and Corollary 10.2 in arXiv:1804.05269v3 give extensions and null Bernoulli factors
    within `ε` of the target. Exactification loops are refuted on nonamenable groups
    (`spectral-gap-refutes-exactification-on-nonamenable-groups`).
  - An approximate isomorphism at level `a` does not make `a` non-rigid.
- **Invariants (no obstruction either way).** Rokhlin entropy is `min(h, s)` and every semicontinuous invariant is
  constant above `s` (`semicontinuous-invariants-blind-above-rokhlin-supremum`). So no known invariant shows a
  level above `s` to be rigid, and none shows it to be non-rigid.
