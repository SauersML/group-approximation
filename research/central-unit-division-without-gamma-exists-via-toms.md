---
rg: 2
id: central-unit-division-without-gamma-exists-via-toms
kind: route
title: Toms's no-Gamma algebra has equal-rank block splittings with growing block counts, so its completion divides the unit centrally but fails Gamma
target: central-unit-division-without-gamma-exists
requires:
  - toms-ah-counterexample-to-uniform-gamma
  - block-balanced-towers-have-central-halving
  - uniform-gamma-iff-completion-has-gamma
  - nuclear-tracial-completions-are-amenable
---

Unreviewed, as an assembly of established nodes. Credit: Toms (arXiv:2606.12188v2, Theorem 5) for the
algebra; CETW Proposition 5.10 and lane `ex-tw-projection-starved-bundle` for the block mechanism.

1. **The algebra.** Let `B` be Toms's simple unital separable nuclear AH algebra without uniform Γ,
   and `(M, X)` its tracial completion with `X = T(B)`. It is factorial by CCEGSTW Proposition
   3.23(iv), since `T(B)` is a face of itself. It is type II_1, since `B` has no finite-dimensional
   representation. It is amenable by the fourth prerequisite.
2. **Blocks.** By the second prerequisite and its artifact
   (`research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md`, Section 3, instance 1):
   - there are stages `m_j < n_j`, `m_j → ∞`, and orthogonal projections `e^{(j)}_1, …, e^{(j)}_{L_j}`
     summing to `1` in `B_{n_j}`;
   - they commute with the image of `B_{m_j}` and have trace `1/L_j` at every trace;
   - `L_j → ∞`, since the block counts `M_i` grow by telescoping.
3. **k-division.** Fix `k`.
   - Group the blocks into `k` consecutive groups of `⌊L_j/k⌋` blocks. Put the `< k` leftover blocks
     in the last group.
   - The group sums `q^{(j)}_1, …, q^{(j)}_k` are orthogonal projections. They are norm-central along
     `j`, since `m_j → ∞` and `∪ B_m` is dense. And `sup_τ |τ(q^{(j)}_i) − 1/k| ≤ k/L_j → 0`.
   - For `‖·‖_{2,X}`-separable `S ⊆ M`, approximate elements of `S` in `‖·‖_{2,X}` by bounded elements of
     `B`. Norm-centrality then gives `‖[q^{(j)}_i, s]‖_{2,X} → 0`.
   - So `p_i = [(q^{(j)}_i)_j] ∈ M^ω ∩ S'` are orthogonal projections with `τ(p_i) = 1/k` at every limit
     trace, hence on `X^ω`.
4. **No property Γ.** By the third prerequisite (CCEGSTW Proposition 5.20), `(M, X)` has property Γ iff
   `B` has uniform property Γ, and `B` does not (first prerequisite).
