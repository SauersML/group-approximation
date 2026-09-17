---
rg: 2
id: diagonally-dominant-integral-matrices-obey-determinant
kind: claim
title: Over every group, self-adjoint diagonally dominant integral matrices have Fuglede--Kadison determinant at least 1
distinct_from:
  determinant-conjecture-holds-for-sofic-groups: that covers every matrix over a sofic group; this covers a restricted class of matrices (symmetric diagonally dominant, any signs) over every countable group, nonsofic ones included.
  finite-spectrum-integral-elements-obey-determinant: that uses finiteness of the spectrum; diagonally dominant operators typically have absolutely continuous spectrum.
  measure-theoretic-determinant-conjecture: that is the open conjecture for integral elements of measured equivalence relations; this is the group-ring case for one class of operators, and its proof uses only a treeable subrelation.
  determinant-violation-needs-nonsofic-support-subgroup: that locates a violation in the group; this restricts which operators can be violations, independently of the group.
---

**ESTABLISHED** by `diagonally-dominant-determinant-spanning-forest-proof`. Not
independently reviewed.

## Statement

Let `G` be a countable group and `T in M_n(Z[G])` self-adjoint, i.e.
`T_ji(g^-1) = T_ij(g)`. Suppose `T` is **symmetric diagonally dominant (SDD)**:

    T_ii(e) >= sum_{(j,g) != (i,e)} |T_ij(g)|     for every i,

with arbitrary signs on the off-diagonal coefficients. Then `T >= 0`, and

    log det_N(G)(T) = integral_{(0,infinity)} log(lambda) d mu_T(lambda) >= 0,

so `det_N(G)(T) >= 1`. Here `mu_T(B) = sum_i <1_B(T) delta_(e,i), delta_(e,i)>`
is the unnormalized spectral measure on `l^2(G)^n`.

On the part of `l^2(G)^n` spanned by the types `i` whose connected component
in the support graph of `T` is infinite, `T` is moreover injective, and
`integral log lambda d mu >= 0` holds with the atom at `0` included.

## Scope

**Operators covered.**
- Combinatorial Laplacians `D - A` of Cayley and Schreier multigraphs of `G`
  with `n` vertex orbits.
- Signless Laplacians `D + A` and signed Laplacians (arbitrary edge signs).
- All of these plus any nonnegative integer potential.
- Every diagonally dominant symmetric M-matrix over `Z[G]`.

**Corollaries.**
- **(Domination.)** If `T in M_n(Z[G])` is self-adjoint with `T >= S >= 0`,
  where `S in M_n(Z[G])` is SDD and injective, then `T` is injective and
  `log det(T) >= log det(S) >= 0`.
- **(Rectangular.)** Since `det(B) = det(B^*B)^(1/2)`, the conclusion holds for
  every `B in M_(m x n)(Z[G])` with `B^*B` SDD. Examples are incidence
  matrices of Cayley and Schreier graphs, with any signs.

## Relation to known results

- **Lyons 2010.** R. Lyons, *Identities and inequalities for tree entropy*,
  CPC 19 (2010), arXiv:0712.3035, gives in its nonnegativity theorem (TeX label
  `t.nonneg`, Section 3) `h(rho) >= 0` for unimodular
  random rooted infinite unweighted graphs. The paper notes that for a Cayley
  graph this means `Det Delta >= 1`.
- **What is new here.** The extension to all SDD matrices. Such a matrix has
  arbitrary signs, integer weights, several vertex orbits, a potential, and
  finite components. The extension goes by domination by a gauge-transformed
  wired spanning forest Laplacian.
- **For the refutation lane.** A counterexample to the determinant conjecture
  cannot be SDD, and it cannot dominate an injective SDD matrix.
