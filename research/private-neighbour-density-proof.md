---
rg: 2
id: private-neighbour-density-proof
kind: route
title: Count the denominator ideal inside a degree box
target: private-neighbour-density
requires: [kun-thom-nonsofic-wreath]
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
---

## Direct proof

`I_f = x^u R₊` is spanned by the monomials `x^{u+β}`, `β ∈ ℕ^d`, so
`I_f ∩ P_L` is spanned by those with `u_j + β_j ≤ L`, giving

```text
dim(I_f ∩ P_L) = ∏_j max(L − u_j + 1, 0),
```

and `κ_u(L)` is the codimension of `I_f ∩ P_L` in `P_L`.  Since `u ≠ 0`,
expanding the product shows `κ_u(L) = (Σ_j u_j)(L+1)^{d−1} + O(L^{d−2})`, so
`κ_u(L) → ∞`.

**Item 1.**  If `a₀ ∈ P_L` solves `af + c ∈ R₊` then `a ∈ P_L` solves it iff
`a − a₀ ∈ I_f`; and `a − a₀ ∈ P_L` because `P_L` is an `F_q`-subspace.  So
the solution set is `a₀ + (I_f ∩ P_L)`, of cardinality
`q^{dim(I_f∩P_L)} = q^{−κ_u(L)}|P_L|`.

**Item 2.**  In the cut step of `minimal-marked-graph-private-neighbour`,
adjacency of `z_a` to competitor `i` is exactly a condition of the form
`af_i + c_i ∈ R₊` with `f_i ∉ R₊`, so by Item 1 it holds for at most a
`q^{−κ_{u_i}(L)}` fraction of `a ∈ P_L`; a union bound over the finitely many
competitors gives the claim.  In the alignment step, condition on all shear
coordinates but the one indexed by a `j₀` with `(g_i)_{j₀k_i} ∉ R₊`; the
remaining coordinate must then avoid a single coset of `I_{f} ∩ P_L`, again
of relative size `q^{−κ_u(L)}`.  Averaging over the conditioning and taking a
union bound over `i` gives the second bound.

The same count replaces the appeal to B. H. Neumann's coset-cover theorem in
`minimal-marked-graph-private-neighbour-proof`: for `L` large the bad
fractions sum to less than one, so a good parameter exists.
