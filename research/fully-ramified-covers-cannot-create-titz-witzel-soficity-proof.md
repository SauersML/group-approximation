---
rg: 2
id: fully-ramified-covers-cannot-create-titz-witzel-soficity-proof
kind: route
title: Fibre sums of local degrees give the mass identity, full ramification makes the top cover an honest covering off the ramification set, and a genuine base component carries flats
target: fully-ramified-covers-cannot-create-titz-witzel-soficity
requires:
  - sparse-fully-branched-covers-iff-sofic-with-connected-links
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Notation is as in the target. `q: X' -> X_0` has degree `M` away from
vertices, and `p_0: X_0 -> Y` has `N_0` sheets. Write `d^q_x` and `d^0_y` for
the local degrees of `q` and `p_0`. Metrics are the intrinsic piecewise
Euclidean length metrics. For a vertex `z` and small `eps > 0`, the ball
`B(z, eps)` is the `eps`-cone on `Lk(z)` (Bridson--Haefliger I.7.39).

## Step 0. Fibre sums

**Lemma 0.** Let `y` be a vertex of `X_0`. Then
`sum_(x in q^(-1)(y)) d^q_x = M`.

*Proof.*
* `Lk(y)` is nonempty. `Lk(y) -> Lk(p_0 y)` is a covering of degree `>= 1`,
  hence onto, and every vertex link of `Y` is nonempty.
* Fix a vertex `e` of `Lk(y)`: the germ at `y` of an edge end. Away from
  vertices, `q` is an honest `M`-sheeted covering, so this germ has exactly
  `M` lifts.
* Each lift is the germ of an edge end at a unique vertex `x` over `y`, that
  is, a vertex of `Lk(x)` over `e`. Every vertex of `Lk(x)` over `e` arises
  this way.
* `Lk(x) -> Lk(y)` is a `d^q_x`-sheeted covering, so `x` accounts for
  exactly `d^q_x` of the `M` lifts. QED

The same argument gives the analogous identity for `p_0` over the vertices
of `Y`.

## Step 1. Mass identity

**Composite.**
* Each closed cell of `X'` maps isometrically onto a closed cell of `X_0`,
  and that cell maps isometrically onto one of `Y`.
* At a vertex `x`, the map `Lk(x) -> Lk(p_0 q x)` is the composite of two
  coverings of finite graphs, so it is a covering, of degree
  `d_x = d^q_x d^0_(qx)`. `Lk(x)` is connected.
* Away from vertices the composite is an honest covering with `N' = M N_0`
  sheets.

So `X' -> Y` is a finite branched cover.

**Branch set.** `d_x >= 2` exactly when `qx in B_0` or `d^q_x >= 2`. By full
ramification, `d^q_x >= 2` exactly when `qx in S`. So
`B' = q^(-1)(B_0 cup S)`.

**Sum.** By Lemma 0,

```text
N' beta(X') = sum_(y in B_0 cup S) d^0_y sum_(x in q^(-1)(y)) d^q_x
            = M sum_(y in B_0 cup S) d^0_y
            = M ( N_0 beta(X_0) + |S \ B_0| ),
```

since `d^0_y = 1` for `y` not in `B_0`. Dividing by `N' = M N_0` gives part 1.

## Step 2. Hitting descends

**Lemma 2.** Put `U = X_0 \ S` and `U' = q^(-1)(U)`. Then `q|: U' -> U` is a
finite covering map and a local isometry.

*Proof.* Take `z in U`.
* If `z` is not a vertex, a small ball about `z` is evenly covered, because
  `q` is an honest covering away from vertices and maps cells isometrically.
* If `z` is a vertex, then `z` is not in `S`. By full ramification,
  `d^q_x = 1` for every `x` over `z`. So `Lk(x) -> Lk(z)` is an isomorphism,
  and `q` maps `B(x, eps)` isometrically onto `B(z, eps)`, as cones on
  isomorphic links.
* For `eps` below half the least distance between distinct points of the
  finite fibre, `q^(-1)(B(z, eps))` is the disjoint union of the
  `B(x, eps)`. Every point of it lies within `eps` of some `x` over `z`,
  because `q` is `1`-Lipschitz on cells and maps the cells at `x` onto the
  cells at `z`.

So `z` is evenly covered by isometric sheets. QED

**Part 2.** Suppose `f: Dbar_R -> X_0` is locally isometric and misses
`S cup B_0`.
* `Dbar_R` is simply connected and locally path connected, and
  `f(Dbar_R) subset U`. So `f` lifts through the covering of Lemma 2 to
  `f': Dbar_R -> U'`.
* `f'` is locally isometric, since `q|U'` is a local isometry.
* `f'` misses `q^(-1)(S) cup q^(-1)(B_0) = B'`. This contradicts (H) for
  `X'`. QED

## Step 3. Fibre cost

Let `C` be an unbranched component of `X_0`, with `n_C` sheets over `Y`.

**`C` is a genuine cover of `Y`, with `n_C <= m`.**
* Every vertex of `C` has `d^0 = 1`. So the argument of Lemma 2, applied to
  `p_0` over all of `Y`, shows that `p_0|C` is a covering map onto its image
  and a local isometry.
* The image is open (covering map) and compact, and `Y` is connected. So
  `p_0|C: C -> Y` is a connected `n_C`-sheeted covering, and
  `C = H \ Delta` for a subgroup `H <= G` of index `n_C`.
* `K cap H` has finite index in `K`. Its normal core in `K` is a
  finite-index normal subgroup of the infinite simple group `K`, so it is
  `K`. Hence `K <= H`, and `n_C = [G : H] <= [G : K] = m`.

**`C` meets `S`.** Suppose not.
* Let `P subset Delta` be an isometrically embedded Euclidean plane, and let
  `f: Dbar_R -> P` be the isometry onto a closed `R`-disk of `P`.
* The universal covering `Delta -> C` is a covering of complexes mapping
  cells isometrically, so it is a local isometry. Composing, `Dbar_R -> C`
  is locally isometric.
* Its image lies in `C`, which misses `B_0` (unbranched) and `S` (by
  assumption). This contradicts Part 2.

**Count.**
* Unbranched components are disjoint, and none meets `B_0`. So
  `|S \ B_0| >= #(unbranched components)`.
* Each unbranched component has at most `m` sheets, and together they carry
  `(1 - phi(X_0)) N_0` sheets. So
  `#(unbranched components) >= (1 - phi(X_0)) N_0 / m`.

Part 1 now gives `beta(X') >= beta(X_0) + (1 - phi(X_0)) / m`. QED

## Step 4. Corollary

Let `X'_n -> X_{0,n} -> Y` be fully ramified towers with (H) and
`beta(X'_n) -> 0`.
* By Part 3, `beta(X_{0,n}) <= beta(X'_n) -> 0`.
* Also by Part 3, `1 - phi(X_{0,n}) <= m beta(X'_n) -> 0`.
* The `X_{0,n}` are nonempty, since `X'_n` is: its mass is defined, so its
  sheet number `N' = M N_0` is positive.

So for large `n` the bases satisfy item 3 of
`sparse-fully-branched-covers-iff-sofic-with-connected-links` with `c = 1/2`.
With connected links, its 3 => 1 gives that `K` is sofic.

For `Y_1^2`:
* `titz-witzel-simple-kazhdan-cat0-lattices-exist` gives that the universal
  cover is a building of type `C~_2` and that the finite residual `K` is
  simple of finite index. It is infinite, since `Delta` is unbounded and the
  action is cocompact.
* Apartments of a Euclidean building are isometrically embedded Euclidean
  planes (Abramenko--Brown, *Buildings*, Thm. 11.16).
* The Corollary of the equivalence records that the links are connected. QED

## Examples of fully ramified towers

Let `D` be the development of a developable complex of groups over `X_0` with
trivial edge and face groups. At the vertex `y` put the finite group
`Q_y = pi_1(Lk(y), *) / N_y`. Let `Gamma` be its fundamental group.
* A lift `yhat` of `y` has stabilizer a conjugate of `Q_y`, and `Lk_D(yhat)`
  is the connected regular cover `L'_y -> Lk(y)` with deck group `Q_y`.
* For a finite-index subgroup `Lambda`, the link of `Lambda \ D` at the image
  of `g yhat` is `L'_y / (Lambda cap g Q_y g^(-1))`. The subgroup
  `Lambda cap g Q_y g^(-1)` acts freely on `L'_y`, being a subgroup of the
  deck group. So this link covers `Lk(y)` with degree
  `|Q_y| / |Lambda cap g Q_y g^(-1)|`.
* If `Lambda` is torsion-free, every such degree is `|Q_y|`.
* If `Lambda` is normal, every such degree is `|Q_y| / |Lambda cap Q_y|`.

Either way the degree is constant on each fibre, so the tower is fully
ramified with `S = {y : Q_y not= 1}` (torsion-free case) or
`S = {y : Q_y not<= Lambda}` (normal case). Every finite regular branched
cover of `X_0` is fully ramified too: its deck group acts transitively on
each fibre and preserves local degrees.

## Remark: components of different degree

Suppose `q` has degree `M_C` over each component `C` of `X_0`, with the `M_C`
possibly different. Let `X_0^#` be the disjoint union, over the components
`C`, of `M_C` copies of `C`, and let `S^#` and `B_0^#` be the copies of `S`
and `B_0`. Then `X_0^#` is a branched cover of `Y` with
`N' = sum_C M_C n_C` sheets.

Lemma 0 holds over each `C` with `M_C` in place of `M`. So the computation of
Step 1 gives

```text
beta(X') = beta(X_0^#) + |S^# \ B_0^#| / N'.
```

Step 3 applies to each unbranched `C` separately. Each copy of `C` meets
`S^#`, which gives
`beta(X') >= beta(X_0^#) + (1 - phi(X_0^#)) / m`.
The Corollary is unchanged, with the `X_0^#` as the certifying bases.

## What a construction must do to escape

It must be *partially ramified* at the last step: some base vertex `y` has
both branched and unbranched points over it. For `Lambda \ D`, `Lambda`
must have torsion and must contain some conjugate of a nontrivial `Q_y`
while meeting another conjugate in a proper subgroup. Then an unbranched
base component can be hit by a few points of a fibre instead of a whole
fibre. In the graph's routes, (V2) and residual finiteness of `Gamma` (and
goodness, through them) are used only to produce a torsion-free subgroup or
a normal finite-index subgroup. Soficity of `pi_1(X)` in
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` part 1 is used
only after the covers exist. So none of these inputs produces such a
`Lambda`. Producing one requires controlling which stabilizer conjugates a
finite-index subgroup swallows, and that is a finite-quotient problem for
`Gamma` of the same kind as the original one.
