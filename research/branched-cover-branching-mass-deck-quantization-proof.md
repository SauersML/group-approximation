---
rg: 2
id: branched-cover-branching-mass-deck-quantization-proof
kind: route
title: Local degrees are deck-invariant and deck transformations act freely on sheets, so each branched deck orbit costs a multiple of |Deck| sheets
target: branched-cover-branching-mass-is-quantized-by-deck-group
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Notation as in the target.  Imports: covering space theory (uniqueness of lifts for connected coverings).
The only literature input is the Titz Mite--Witzel fact, recorded verbatim in
`titz-witzel-simple-kazhdan-cat0-lattices-exist`, that "the finite residual ... has FINITE INDEX".  That
fact is used only in the corollary.

Write `X°` for `X` minus its vertex set and `Y°` for `Y` minus its vertex set.  By the definition of a
finite branched cover, `p: X° -> Y°` is a covering map of degree `N`.

## Step 1. `X°` is connected

`X` is connected.  A path in `X` between points of `X°` can be moved off the vertices, as follows.
* Near a vertex `x`, a small closed star of `x` minus `x` is homeomorphic to `Lk(x) x (0, 1]`.
* `Lk(x)` is connected by definition.
* So an arc entering and leaving `x` can be replaced by an arc in this punctured star joining its entry
  and exit points.

The path is piecewise linear and meets only finitely many vertices, so the replacements are finitely many.
Two points of `X°` lying in open cells are therefore joined in `X°`.  Every point of `X°` lies in the
closure of an open 2-cell, because `Y` is pure and `p` maps cells onto cells.  Hence `X°` is connected.

## Step 2. `D` acts freely on sheets

Let `g` be in `D`.  Then `g` restricts to a deck transformation of the connected covering `X° -> Y°`.
* If `g` fixes one point of `X°`, then `g` is the identity on `X°`, by uniqueness of lifts.
* `X°` is dense in `X`, so `g` is then the identity on `X`.

Fix a vertex `y` of `Y` and a corner of a 2-cell at `y`, that is, an edge `c` of `Lk(y)`.  Choose a point
`t` in the open 2-cell of `c`, near that corner.  Let `F_c = p^(-1)(t)`.  Then `|F_c| = N`, `D` preserves
`F_c`, and `D` acts freely on it.  So every `D`-orbit in `F_c` has exactly `|D|` points.

## Step 3. Sheets through a vertex

Each point `s` of `F_c` lies in a unique open 2-cell `sigma_s` of `X` lying over the cell of `t`.  The
corner of `sigma_s` over the corner `c` is a vertex `x(s)` over `y`, with an edge `e(s)` of `Lk(x(s))`
lying over `c`.  The resulting map `phi: F_c -> p^(-1)(y)` has two properties.
* **Fibre sizes.**  `s -> e(s)` is a bijection from `phi^(-1)(x)` onto the set of edges of `Lk(x)` over
  `c`.  The map `Lk(x) -> Lk(y)` is a covering of degree `d_x`, so `|phi^(-1)(x)| = d_x`.
* **Equivariance.**  `g` maps cells to cells over the same cells of `Y`, so `phi(g s) = g phi(s)`.

In particular `sum_(p x = y) d_x = N`, which is the identity already used to define `beta`.

## Step 4. `d_x` is `D`-invariant

For `g` in `D`, `g` induces a graph isomorphism `Lk(x) -> Lk(gx)`.  This isomorphism commutes with the
covering maps to `Lk(y)`, because `p g = p`.  So `d_(gx) = d_x`, and `B` is `D`-invariant.

## Step 5. Quantization and gap

Let `O = D x` be an orbit in `p^(-1)(y)`.
* `phi^(-1)(O)` is `D`-invariant, by Step 3, and has `|O| d_x` points, by Steps 3 and 4.
* By Step 2 it is a disjoint union of free `D`-orbits.
* So `|O| d_x` is a multiple of `|D|`.  If `O` is nonempty, it is at least `|D|`.

The branched mass over `y` is `(1/N) sum_(O in B over y) |O| d_O`.  It is therefore a nonnegative
integer multiple of `|D|/N`.  It is at least `|D|/N` whenever some vertex over `y` branches.  Summing over
the vertices `y` of `Y` gives parts 1 and 2.
* Part 2 says `beta >= 1/k` with `k = N/|D|`.  This `k` is an integer: it is the number of `D`-orbits on
  `F_c`.
* Part 3 is the case `|D| = N`.  The branched mass over each `y` is then an integer between 0 and 1.
  It is at most `(1/N) sum_x d_x = 1`.  So `beta` is an integer between 0 and the number of vertices of `Y`.

## Step 6. Corollary

Suppose `beta(X) = 0`.
1. Every `d_x = 1`, so `p` is a local homeomorphism at every vertex, since the links map isomorphically.
2. So `p: X -> Y` is a covering map of connected complexes, of degree `N`.
3. It corresponds to a subgroup of index `N` in `pi_1(Y)`.
4. That subgroup contains the finite residual, which has index `r`.  So `N <= r` (indeed `N` divides
   `r`).

Now let `N_n > r` and `beta(X_n) -> 0`.
1. Then `beta(X_n) > 0`, so `B_n` is nonempty.
2. Part 2 gives `|D_n|/N_n <= beta(X_n)`.

For `Y_1^2`, the finite residual is the kernel `Gamma_1^2`, of index 2, as recorded on
`titz-witzel-kernel-sofic`.

## Step 7. The coset description

For a connected covering `X° -> Y°` corresponding to `H <= F = pi_1(Y°)` of index `N`, the deck group of
the covering is `N_F(H)/H`.
* Every deck transformation of `X°` extends uniquely to `X`.
  - The vertices of `X` over `y` are in bijection with the connected components of the preimage of a
    small punctured open star of `y`.  Each such component is `Lk(x) x (0,1)`, which is connected.
  - A deck transformation of `X°` permutes these components, so it extends continuously and cellularly.
* So `D = N_F(H)/H`, and `|D|/N = 1/[F : N_F(H)]`.
* If `[F : N_F(H)] <= k` along a sequence, then part 2 gives `beta >= 1/k` or `beta = 0`.  So such a
  sequence is never sparse beyond degree `r`.

Only the formula `D = N_F(H)/H` is used.  No rank of `F` is claimed in this route.
