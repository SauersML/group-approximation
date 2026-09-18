---
rg: 2
id: artin-ghost-ideals-reduce-to-four-lanner-trees-proof
kind: route
title: "Proof: slice along a minimal non-spherical parabolic subgroup; those are free, affine or Lannér, and all but four Lannér trees satisfy the K(π,1) conjecture"
target: artin-ghost-ideals-reduce-to-four-lanner-trees
requires:
  - artin-ghost-ideal-localizes-to-standard-parabolics
  - deligne-connectivity-iff-artin-complex-connectivity
  - affine-artin-groups-satisfy-k-pi-1-conjecture
  - two-dimensional-artin-groups-satisfy-k-pi-1-conjecture
  - artin-groups-of-rank-at-most-four-satisfy-k-pi-1
---

**Literature inputs.**

- For a Coxeter system `(W_M, M)` with finite labels let `B_M = (−cos(π/m_st))`. `W_M` is finite
  iff `B_M` is positive definite. If `B_M` is positive semidefinite and degenerate and `M` is
  irreducible, `W_M` is an irreducible affine Coxeter group (J. E. Humphreys, *Reflection
  groups and Coxeter groups*, §2.3–2.7 and §6.5).
- `W_M` is *compact hyperbolic* when `B_M` is nondegenerate, not positive definite, and every
  proper subdiagram is of finite type. These are Lannér's groups: the triangle groups with
  `1/p + 1/q + 1/r < 1` in rank 3, nine groups in rank 4, five in rank 5 and none in rank at
  least 6 (Humphreys §6.8–6.9, Table 6.9, after F. Lannér 1950). The five in rank 5 are the
  paths `[5,3,3,3]`, `[4,3,3,5]`, `[5,3,3,5]`, the tree `[5,3,3^{1,1}]` and the 5-cycle with
  labels `(3,3,3,3,4)`.
- The Artin group of the 5-cycle `(3,3,3,3,4)` satisfies the K(π,1) conjecture (J. Huang,
  arXiv:2305.16847, Invent. Math. 238 (2024); recorded in
  `compact-hyperbolic-4-simplex-artin-groups-satisfy-k-pi-1`, not checked against the
  theorem statement in this pass).

**Step 1 (minimal non-spherical subsets).** Let `M ⊆ S` be minimal non-spherical.

- `M` is irreducible: if `M = M_1 ⊔ M_2` with no edges between them and both nonempty, then
  `W_M = W_{M_1} × W_{M_2}` is a product of two finite groups.
- If `|M| = 2`, then `m_st = ∞`.
- If `|M| ≥ 3`, every pair in `M` is spherical, so all labels are finite. Every proper
  principal submatrix of `B_M` is positive definite, so by Cauchy interlacing `B_M` has at
  least `|M| − 1` positive eigenvalues. `B_M` is not positive definite. Either it is
  degenerate, hence positive semidefinite, and `W_M` is irreducible affine; or it has
  signature `(|M| − 1, 1)` and `W_M` is compact hyperbolic, so `|M| ≤ 5`.

**Step 2 (K(π,1) implies no ghosts).** If `A_M` satisfies the K(π,1) conjecture and `W_M` is
infinite, then `Δ(A_M)` is contractible and `G(A_M) = 0`. This is the `k = ∞` consequence
recorded in `deligne-connectivity-iff-artin-complex-connectivity`, with
`artin-complex-top-homology-is-intersection-of-ideals` for the identification
`G(A_M) = H_{|M|−1}(Δ(A_M))`. For `|M| ≥ 2` the top degree is positive, so contractibility
kills it.

**Step 3 (known minimal cases).** Let `M` be minimal non-spherical and not one of the four
trees. Then `G(A_M) = 0`:

- `|M| = 2`, `m_st = ∞`: the free rank-two case of
  `artin-ghost-ideal-localizes-to-standard-parabolics`.
- `W_M` affine: `affine-artin-groups-satisfy-k-pi-1-conjecture` and Step 2.
- `W_M` compact hyperbolic of rank 3: every spherical subset has at most 2 elements, so
  `two-dimensional-artin-groups-satisfy-k-pi-1-conjecture` and Step 2.
- `W_M` compact hyperbolic of rank 4: `artin-groups-of-rank-at-most-four-satisfy-k-pi-1` and
  Step 2.
- `W_M` compact hyperbolic of rank 5 and not a tree: it is the 5-cycle `(3,3,3,3,4)`, covered by
  Huang's theorem and Step 2.

**Step 4 (item 1).** `A_M` is the Artin group of the induced subdiagram. By Step 3,
`G(A_M) = 0`, and by `artin-ghost-ideal-localizes-to-standard-parabolics` with `T = M`,
`G(A_Λ) = 0`. ∎

**Step 5 (item 2).** (a) ⟹ (b) is a special case, since the four trees have infinite Coxeter
groups. For (b) ⟹ (a), let `W_Λ` be infinite and pick a minimal non-spherical `M ⊆ S` (it
exists since `S` is finite and `W_∅` is finite). If `M` is not one of the four trees, apply
item 1. If it is, (b) gives `G(A_M) = 0`, and the localization theorem again gives
`G(A_Λ) = 0`. ∎
