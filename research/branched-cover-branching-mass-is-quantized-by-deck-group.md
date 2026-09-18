---
rg: 2
id: branched-cover-branching-mass-is-quantized-by-deck-group
kind: claim
title: The branching mass of a connected branched cover is an integer multiple of |Deck|/N, so symmetric branched covers of a non-residually-finite 2-complex are never sparse
distinct_from:
  sparse-branched-covers-with-sofic-pi1-give-sofic-lattice: that transfers soficity from sparse branched covers to the base; this is a quantization of the branching mass by the deck group, which excludes every symmetric sparse cover.
  radu-square-complex-flat-hitting-sparse-branched-covers: that asks for sparse flat-hitting covers of Radu's complex; this uses no flat hitting, no girth and no product structure, and forbids every symmetric sparse cover of any locally CAT(0) 2-complex.
  kazhdan-ergodic-sofic-centralizer-forces-lef: that is an ultraproduct theorem for property (T) groups with an ergodic centralizer; this is a finite, exact count for branched covers of any locally CAT(0) 2-complex, with no property (T).
  deligne-bounded-rank-monomial-models-need-large-detecting-cycles: that counts defective cells on deck translates of a detecting 2-cycle in twisted monomial models of Deligne covers; this counts branch sheets on deck orbits of vertex fibres in branched covers.
  titz-witzel-flat-hitting-sparse-branched-covers: that is an existence statement; this kills the symmetric constructions of the covers it asks for.
---

**ESTABLISHED** (proof: `branched-cover-branching-mass-deck-quantization-proof`).

**Setting.**  `Y`, finite branched covers `p: X -> Y`, the local degrees `d_x`, the branch set `B`, the
degree `N` and the branching mass `beta(X) = (1/N) sum_(b in B) d_b` are as in
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`.  In addition, `Y` is pure 2-dimensional and
no edge of `Y` is free (every vertex link of `Y` is a graph with no isolated vertex).  Both conditions
hold for `Y_1^2` and for Radu's square complex `S_R`.  Let `X` be connected, and let
`D = Deck(X/Y)` be the group of cellular automorphisms `g` of `X` with `p g = p`.

**Theorem.**
1. **(Quantization.)** `beta(X)` lies in `(|D|/N) Z_(>=0)`.  More precisely, for each vertex `y` of `Y`
   the branched mass over `y`, `(1/N) sum_(b in B, p b = y) d_b`, is a nonnegative integer multiple
   of `|D|/N`.
2. **(Gap.)** If `B` is nonempty, then `beta(X) >= (|D|/N) * #{y : p^(-1)(y) meets B}`.  So
   `beta(X) >= 1/k`, where `k = N/|D|` is the number of `D`-orbits on the sheets.
3. **(Galois covers.)** If `X -> Y` is Galois off the vertices (`D` transitive on the sheets), then
   `beta(X)` is an integer between `0` and the number of vertices of `Y`.

**Corollary (non-residually-finite bases).**  Suppose the finite residual of `pi_1(Y)` has finite index
`r`.  Then every connected branched cover with `beta(X) = 0` has `N <= r`.  Hence every sequence of
connected branched covers `X_n` with `N_n > r` and `beta(X_n) -> 0` satisfies

```text
|Deck(X_n / Y)| / N_n  <=  beta(X_n)  ->  0 .
```

For `Y = Y_1^2`, `r = 2` (Titz Mite--Witzel Theorem A: the finite residual has finite index, and the
kernel `Gamma_1^2` has index 2).

**What dies.**  The following constructions cannot produce the sparse covers of
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` (part 2), of
`titz-witzel-flat-hitting-sparse-branched-covers`, or of the Titz--Witzel side of any sparse-cover route,
unless their symmetry ratio `|D|/N` tends to zero.
* Galois branched covers, whose deck group is transitive on sheets.  These include every
  Cayley-complex construction from a finite group `Q` that is a quotient of `pi_1(Y minus vertices)`,
  with `X` minus its vertices the corresponding regular cover.  They have `beta` in `{0, 1, ..., 7}`.
* Coset constructions.  Here `X` minus its vertices corresponds to a subgroup `H` of index `N` in
  `F = pi_1(Y minus vertices)`, and `D = N_F(H)/H`.  They die whenever
  `[F : N_F(H)]` stays bounded, that is, whenever `H` has boundedly many conjugates.
* Any equivariant construction in which a finite group of automorphisms over `Y` acts with boundedly
  many orbits on the sheets.

**The invariant and the dying step.**  The invariant is the local degree `d_x`, which is constant on
`D`-orbits, together with the fact that `D` acts freely on the sheets.  The dying step is the first
branch vertex.  It forces its whole `D`-orbit to branch, and that orbit carries a union of free
`D`-orbits of sheets, so it costs at least `|D|` sheets.

**Reading.**  A sparse branched cover of `Y_1^2` of large degree has asymptotically trivial symmetry, like
a sparse cover of `S_R` under (H).  Normality or near-normality, the usual source of explicit finite
complexes, is exactly what is forbidden.  Explicit candidates for the open existence prerequisites must
be asymmetric.  For example, they can be built from non-normal subgroups of `pi_1(Y minus vertices)` with many conjugates,
or by inhomogeneous surgery.  This turns the heuristic recorded in the Attempts section of
`titz-witzel-kernel-sofic` (Galois branched covers have a linear defect) into a theorem.  It also extends
the heuristic from Galois covers to all covers with `|D| >= cN`.
