---
rg: 2
id: tripod-free-integral-matrices-virtually-cyclic-proof
kind: route
title: Branching of a breadth-first tree past depth k forces a tripod, so tripod-free graphs have bounded spheres, virtually cyclic stabilizers and a sofic decomposition
target: tripod-free-integral-matrices-reduce-to-virtually-cyclic
requires:
  - determinant-conjecture-holds-for-sofic-groups
  - integral-eigenvalues-galois-balanced-for-sofic-groups
  - determinant-conjecture-iff-serre-class-spectra
artifacts:
  - research/artifacts/determinant-norm-room-2026-09-16.md
---

Full proofs are in the artifact (Sections 1--3). Sketch:

**1. Branching lemma.** Fix a vertex `v`, a breadth-first spanning tree `T`,
and `r`. Let `L_j` be the set of vertices at distance `j` having a
`T`-descendant at distance `r`. If some `x in L_j` with `k <= j <= r - k` has
two children in `L_(j+1)`, then three legs form `T_(k,k,k)` at `x`:
- the ancestor path of `k` edges;
- two descending paths of `k` edges, through distinct children.

Levels and disjoint subtrees keep the legs apart.

**2. Bounded spheres.** `|L_j|` is nondecreasing, and it is constant for
`k <= j <= r-k+1` by 1. Hence

```text
|S_r| = |L_r| <= (Delta - 1)^(k-1) |L_k| <= Delta^(2k).
```

**3. Stabilizers.** A component `C` carries a free action of `K_C` with at most
`n` orbits. By Švarc--Milnor, `K_C` is finitely generated and quasi-isometric
to `C`, and by 2 its growth is linear. A finitely generated group of linear
growth is finite or virtually infinite cyclic.

**4. Decomposition.** Identify `(k h_j, j)` with `(k, j)` for `k in K_C`. This
turns `r_A` on `l^2(C)` into `r_(A_C)`, where `(A_C)_ij(x)` is the coefficient
of `A_ij` at `h_i^-1 x h_j`. `G`-invariance of the diagonal matrix coefficients
gives `mu_A = sum_C mu_(A_C)`.

**5. Consequences.** Virtually cyclic groups are amenable, hence sofic, so each
`mu_(A_C)` obeys every Serre inequality. This uses
`determinant-conjecture-holds-for-sofic-groups` and
`determinant-conjecture-iff-serre-class-spectra` over `K_C`. Masses add, and
`integral-eigenvalues-galois-balanced-for-sofic-groups` gives balanced
eigenvalues.

**6. Norm criterion.** Use the Schur test with weights `2^(-j/2)`, and the
Rayleigh quotient of the same vector:

```text
6 * 2^(-1/2) (2 - 2^(1-k)) / (4 - 3 * 2^(-k))
  <= rho(T_(k,k,k))
  <= 3/sqrt 2.
```

A tree subgraph `T` of `Gamma_A` is dominated entrywise by the principal
submatrix of `r_|A|`. By Perron--Frobenius and compression,
`rho(T) <= ||r_|A|||`. Choose `k` with the lower bound above `||r_|A|||`.
