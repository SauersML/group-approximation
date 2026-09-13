---
rg: 2
id: block-balanced-towers-have-central-halving
kind: claim
title: Towers whose connecting maps split into equal-rank orthogonal blocks have norm-central halving projections
distinct_from:
  point-dominated-diagonal-ah-has-uniform-gamma: that balances central projections against every element on all limit traces under a point-dominance hypothesis; this only halves the trace of the unit, with no dominance hypothesis, and allows nontrivial twisted units.
  asymptotically-clustered-diagonal-ah-has-uniform-gamma: that needs clustered eigenmap packets to get uniform Gamma; this needs only equal block ranks and gets the unbalanced halving condition.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Let `A = lim (A_n, φ_n)` be a unital separable inductive limit. Suppose there are
stages `m_j < n_j` with `m_j → ∞`, and pairwise orthogonal projections
`e^{(j)}_1, …, e^{(j)}_{L_j} ∈ A_{n_j}` summing to `1`, such that:
- each `e^{(j)}_b` commutes with `φ_{m_j,n_j}(A_{m_j})`;
- `τ(e^{(j)}_b) = 1/L_j` for every `b` and every trace `τ` of `A_{n_j}`;
- `L_j ≥ 2`, and `1/2 − ⌊L_j/2⌋/L_j → 0`; for example every `L_j` is even, or `L_j → ∞`.

Then `A` has central halving, witnessed by projections `p_j` with `‖[p_j, a]‖ → 0` in
norm for every `a ∈ A` and `sup_{τ∈T(A)} |τ(p_j) − 1/2| ≤ 1/(2L_j)`.

**Block splittings give the hypothesis.** Suppose
`φ_{m,n} = Σ_b φ^{(b)}`, a sum of `*`-homomorphisms with orthogonal ranges and
`Σ_b φ^{(b)}(1) = 1`. Then `e_b = φ^{(b)}(1)` commutes with the image. In a corner
`q_n(C(X_n) ⊗ K)q_n`, equal constant block ranks give `τ(e_b) = 1/L`.

**Instances** (verified against the sources in the artifact, Section 4):
- Toms's non-simple Thom–Porteous tower and his simple no-Γ algebra `B`
  (arXiv:2606.12188v2, Sections 4 and 7). Their blocks are line-bundle-twisted coordinate
  pullbacks and point evaluations, all of rank `rank(s_i)`.
- The Dadarlat–Hirshberg–Toms–Winter algebra with no unital `Z_{3,4}`
  (arXiv:0712.2020), and Hirshberg–Rørdam–Winter products `⊗_j B_j`. There the blocks
  are `1 ⊗ e_{i+1}` and `1 ⊗ f_{i+1}`.
- Diagonal AH algebras with `n_i → ∞`, which is CETW's case, and all their corners
  `p A p` by projections from a finite stage, such as the Hopf corners of Villadsen
  first-type algebras.
