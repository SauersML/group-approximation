---
rg: 2
id: rokhlin-excess-never-drops-under-bernoulli-transfers-proof
kind: route
title: Pull back small generators to bound suprema along subgroups, then show the family of pairs above supremum plus path defect is closed under every transfer
target: rokhlin-excess-never-drops-under-bernoulli-transfers
requires:
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - bernoulli-isomorphism-collapse-set-is-a-subgroup
  - bernoulli-entropy-counterexample-constraints
  - bernoulli-collapse-is-null-or-eventually-total
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
artifacts:
  - research/artifacts/rokhlin-excess-transfer-lyapunov-2026-09-17.md
---

"Section n" refers to the artifact. The prerequisites supply:
- the formula `h^Rok_G(L^G) = min(H(L), s(G))` (item 1 of the first);
- translation, co-induction, restriction and the threshold `min(a, b) ≥ s` (items 1, 6 and 7 of the second, and
  proof (d) of the third, which also identifies `L^G` restricted to an index-`k` subgroup with base `L^k`);
- upward closure of `R(G)` inside `[s, ∞)` (item 3 of the fourth);
- well-definedness of `X_h` (the fifth).

**Item 1 (Section 1).**
- *Overgroups.* Take `H(L) > s(G)`. A `G`-generator `β` of `L^G` of entropy `< s(G) + ε` pulls back along the
  restriction map `L^Γ → L^G`. Its `Γ`-translates contain the coordinate at `e`, so they generate `L^Γ`. The formula
  over `Γ` gives `min(H(L), s(Γ)) ≤ s(G)`, hence `s(Γ) ≤ s(G)`.
- *Finite index.* The join of `k` coset translates of a `G`-generator is an `H`-generator of entropy
  `≤ k(s(G) + ε)` for the `H`-Bernoulli shift with base `L^k`. The formula over `H` gives `s(H) ≤ k s(G)`.

**Item 2 (Section 2, Theorem 2.3).**
- Let `F` relate `a, b` over `Γ` iff `a = b`, or `min(a, b) ≥ s(Γ) + δ_S(Γ)`.
- `F` is an equivalence relation, and it contains the seeds (empty path).
- It is closed under translation.
- It is closed under co-induction, since extending paths gives `δ_S(Γ) ≤ δ_S(G) + s(G) − s(Γ)`.
- It is closed under restriction, since `δ_S(H) ≤ k δ_S(G) + k s(G) − s(H)`.
- Defects are non-negative by item 1. So `T(S) ⊆ F`.

**Item 3 (Corollary 3.1).** Apply item 2, using `E(p, e) ≥ e + Σ defects`.

**Item 4 (Theorem 3.2).**
- Push near-threshold pairs along co-induction or restriction, and conclude with upward closure.
- At `s = 0`, item 1 forces supremum `0` on every overgroup and every finite-index subgroup.

**Item 5 (Proposition 3.3).**
- Co-induction pushes every nontrivial pair up, so `r(G) ≥ r(Γ)`.
- Restriction gives `r(H) ≤ k r(Γ)`.
- The failure statement is the contrapositive of item 4.
