---
rg: 2
id: kervaire-killing-form-via-stable-ac-and-torsion-free-lots
kind: route
title: Stable Andrews--Curtis and torsion-free LOT groups forbid balanced Kervaire failures, and positive deficiency forbids the rest
target: kervaire-killing-form-holds-over-nonnegative-deficiency-groups
requires:
  - stable-andrews-curtis-conjecture
  - lot-groups-are-torsion-free
  - balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free
  - deficiency-zero-kervaire-failure-yields-whitehead-counterexample
artifacts:
  - research/artifacts/ideas-bridges-2-2026-09-14.md
---

Let `G != 1` have a finite presentation `<x_1, ..., x_n | r_1, ..., r_m>` with
`m <= n`, and let `w in G * <t>`.

- **If `m < n`:** item 1 of
  `deficiency-zero-kervaire-failure-yields-whitehead-counterexample` makes `G_w`
  infinite.
- **If `m = n` and `G_w = 1`:**
  1. By item 2 of the same theorem, `P_w = <x_1, ..., x_n, t | r_1, ..., r_n, W>`
     is a balanced presentation of the trivial group.
  2. By `stable-andrews-curtis-conjecture`, `P_w` is stably AC-trivial.
  3. Item 1 of `balanced-kervaire-failure-refutes-stable-ac-or-lot-torsion-free`
     then gives a LOT group `G(Gamma) = G * Z` with torsion.
  4. This contradicts `lot-groups-are-torsion-free`.

So `G_w != 1` in both cases.

**Comparison.**
- `nonnegative-deficiency-kervaire-via-finite-whitehead` needs Whitehead's
  conjecture.
- `kervaire-killing-form-via-one-cell-whitehead` needs its one-cell case, which
  contains asphericity of every LOT complex.
- This route trades asphericity for torsion-freeness of LOT groups, a strictly
  weaker property, at the price of stable Andrews--Curtis. Stable AC is widely
  expected to fail, so the useful direction is the contrapositive: a balanced
  failure refutes stable AC or puts torsion into a LOT group.
