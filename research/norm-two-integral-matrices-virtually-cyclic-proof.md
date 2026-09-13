---
rg: 2
id: norm-two-integral-matrices-virtually-cyclic-proof
kind: route
title: Balls of the matrix graph are cyclotomic, so McKee--Smyth forces linear growth, virtually cyclic component stabilizers, and a sofic decomposition
target: norm-two-integral-matrices-reduce-to-virtually-cyclic-groups
requires:
  - cyclotomic-integer-matrices-classified
  - determinant-conjecture-holds-for-sofic-groups
  - integral-eigenvalues-galois-balanced-for-sofic-groups
  - determinant-conjecture-iff-serre-class-spectra
---

Write `r_A` as an integer symmetric matrix on the basis `delta_(g,i)`, with
finitely many nonzero entries in each row. Left translation by `G` commutes with
`r_A` and acts freely on `G x [n]`, preserving `Gamma_A`.

**1. Balls are cyclotomic.** Let `B = B_r(v)`.
- The principal submatrix of `r_A` on `B` is a compression of an operator of norm
  at most `2`, so it is a finite cyclotomic matrix.
- A geodesic from any `u in B` to `v` stays in `B`, so its graph, the induced
  subgraph on `B`, is connected, and `dist_B(u, v) <= r`.

**2. Linear growth.**
- By Theorem 3 of `cyclotomic-integer-matrices-classified`, that submatrix is
  contained, up to equivalence, in a maximal indecomposable cyclotomic matrix
  `M`. Equivalence does not change graphs, and containment is an induced
  subgraph, so distances in `M` are at most distances in `B`.
- Hence `B` lies in the `r`-ball of `M` around `v`.
- In `T_(2k)`, `C^(++)_(2k)` and `C^(+−)_(2k)` edges join only same or consecutive
  rungs, so that ball has at most `2(2r+1)` vertices. The other maximal matrices
  have at most `16` vertices.
- So `|B_r(v)| <= max(16, 4r+2)`.

**3. Stabilizers.** Let `C` be a component and `K_C = {g : gC = C}`.
- If `(h, j)` and `(h', j)` lie in `C`, then `h'h^-1` maps the first to the
  second. Components are equal or disjoint, so `h'h^-1 in K_C`. So `K_C` acts
  freely on `C` with one orbit on each nonempty `C cap (G x {j})`.
- `C` is connected and locally finite and the action is cocompact, so by
  Švarc--Milnor `K_C` is finitely generated and quasi-isometric to `C`.
- `K_C` therefore has linear growth, and a finitely generated group of linear
  growth is finite or virtually infinite cyclic.

**4. Decomposition.**
- Each `(e, j)` lies in exactly one component, so `[n]` is partitioned by the
  sets `J_C` over representatives `C` of the `G`-orbits of components.
- Pick `(h_j, j) in C` for `j in J_C`. Then `C = disjoint union of K_C (h_j, j)`,
  and `r_A` restricted to `l^2(C)` commutes with `K_C`, so it is right
  multiplication by some `A_C in M_(J_C)(Z[K_C])`.
- By `G`-invariance, the root spectral measure at `(e, j)` equals the one at
  `(h_j, j)`, which is that of `A_C` at `(e, j)`. Summing over `j in J_C` gives
  `|J_C| mu_(A_C)`, hence `mu_A = sum_C (|J_C|/n) mu_(A_C)`.

**5. Consequences.** Each `K_C` is amenable, hence sofic.
- `mu_(A_C)` obeys every Serre inequality
  (`determinant-conjecture-holds-for-sofic-groups` with
  `determinant-conjecture-iff-serre-class-spectra`). The Serre class is convex,
  so `mu_A` obeys them too, and (FC) gives `det r_(Q(A)) >= 1`.
- By Thom (`integral-eigenvalues-galois-balanced-for-sofic-groups`) the
  eigenvalues of each `A_C` are algebraic integers whose conjugates are
  eigenvalues with equal multiplicity. Masses add over `C`, so the same holds
  for `A`.
- All conjugates lie in `[-2, 2]`, so by Kronecker each eigenvalue is
  `2cos(2 pi r)`.
- Finite and amenable matrices give integer-matrix spectral limits, and convex
  combinations with real weights are approximated by rational ones. QED
