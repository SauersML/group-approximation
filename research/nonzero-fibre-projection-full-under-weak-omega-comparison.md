---
rg: 2
id: nonzero-fibre-projection-full-under-weak-omega-comparison
kind: claim
title: If Cu(C(X)) has weak omega-comparison, properly infinite projections in M(C(X) ⊗ K) with nonzero fibres are full
distinct_from:
  self-similar-hilbert-cx-module-has-unit-section: that proves unit sections exist and fullness for finite-dimensional X; this proves fullness whenever Cu(C(X)) has weak omega-comparison, via property (S).
artifacts:
  - research/artifacts/k1-defect-ideal-corona-converse-2026-09-13.md
---

Let X be compact metrizable and `P ∈ M(C(X) ⊗ K)` a properly infinite projection whose fibres are all
nonzero. Put `E_P = P H_X` and `D_P = P(C(X) ⊗ K)P`.

1. The following are equivalent:
   - P is full;
   - `P ~ 1`, that is, `E_P ≅ H_X`;
   - `D_P` is stable;
   - (AO) finitely many sections of `E_P` always admit a unit section uniformly almost orthogonal to them.
2. `D_P` always has property (S): no nonzero unital quotient and no nonzero bounded 2-quasitrace.
3. If `Cu(C(X))` has weak ω-comparison, then P is full.
4. Consequence for the Toeplitz defect ideal J of `T_2 * T_2`. Let `π: T_2 * T_2 -> L(E)` be a
   representation over such an X with compact defect `π(iota_1(p_3))`, nondegenerate on `π(J)` and with
   nonzero fibres. Then every unitary of `J~` becomes null in `K(E)~`.

A counterexample needs a base on which weak ω-comparison fails. `X = ∏ S²` is one. The unconditional
statement is the open claim `properly-infinite-nonzero-fibre-projection-is-full`.
