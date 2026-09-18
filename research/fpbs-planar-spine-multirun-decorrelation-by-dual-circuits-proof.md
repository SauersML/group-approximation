---
rg: 2
id: fpbs-planar-spine-multirun-decorrelation-by-dual-circuits-proof
kind: route
title: A declared-open run misses infinity exactly when a dual circuit surrounds it; cutting the dual at the bisector of the two sides makes the half-plane events independent and blind to the other side's pattern, and Harris returns to the one-sided events at the cost of circuits that leave the half-plane, which must reach distance delta/2
target: fpbs-planar-spine-multirun-decorrelation-by-dual-circuits
requires:
  - fpbs-path-bridge-ratio-untilted-coverage-decorrelation
---

Notation as in the target. `omega` is Bernoulli(`p'`) bond percolation on
`Z^2` with `p' > 1/2`. The path `x_0 ... x_n` has distinct vertices and
edges `e_i = x_{i-1} x_i`. The split edge is `e_k`, and
`S = S^- ⊔ S^+ ⊆ Lambda \ {e_k}` with `S^- ⊆ {e_1,...,e_{k-1}}` and
`S^+ ⊆ {e_{k+1},...,e_n}`. So `V(S^-) ⊆ U^- = {x_0,...,x_{k-1}}` and
`V(S^+) ⊆ U^+ = {x_k,...,x_n}`.

## 0. Reduction to the attachment function

For a finite edge set `F`, let `q(F)` be the probability that every run
(maximal block of consecutive edges) of `F` lies in an infinite cluster of
`omega ∪ F`. The event `{F ⊆ Z}` says that every edge of `F` is open and
every run of `F` meets the infinite cluster. Given that `F` is open,
`omega = omega ∪ F`, and the second event does not depend on the states of
the edges of `F`. Hence `P(F ⊆ Z) = p'^{|F|} q(F)`. Since
`|S| = |S^-| + |S^+|`, the powers of `p'` cancel and

```text
P(S ⊆ Z) / ( P(S^- ⊆ Z) P(S^+ ⊆ Z) ) = q(S) / ( q(S^-) q(S^+) ).       (0.1)
```

This is the reduction already used in Theorem 2 of
`fpbs-path-bridge-ratio-untilted-coverage-decorrelation`.

## 1. Dual description

The dual lattice `(Z^2)^* = Z^2 + (1/2,1/2)` has one dual edge `e^*` crossing
each primal edge `e`, with the same midpoint `m(e)`. For a configuration
`eta ⊆ E(Z^2)`, call `e^*` *dual-open* when `e notin eta`. When `eta` is
Bernoulli(`p'`) on all edges except a finite set `F` declared open, the
dual-open set is a product measure: `e^*` is dual-open with probability
`1-p'` for `e notin F`, and never for `e in F`. Call this measure `P_F`.

**Lemma 1.1 (planar duality).** Let `W` be a finite connected vertex set.
Then `W` lies in a finite cluster of `eta` iff some dual-open circuit
surrounds a vertex of `W`. If `W = V(R)` for a run `R ⊆ F`, a dual-open
circuit that surrounds one vertex of `W` surrounds all of `W`.

*Proof.* The first statement is the standard duality for bond percolation on
`Z^2` (for example Grimmett, *Percolation*, Section 11.2, or Kesten's
book). The boundary of a finite cluster is a dual circuit of closed primal
edges surrounding it. Conversely, a surrounding dual-open circuit separates
the enclosed vertices from infinity in `eta`. For the second statement: the
edges of `R` are declared open, so their duals are never dual-open, and a
dual-open circuit does not cross them. So `W` is joined by curves that
avoid the circuit, and lies on one side of it. `□`

Consequently, with `P = P_F`,

```text
q(F) = P_F( no dual-open circuit surrounds any vertex of V(F) ).       (1.1)
```

Every event of the form "no dual-open circuit of a given kind surrounds a
vertex of a given set" is **decreasing** in the dual-open set. Harris's
inequality holds for any product measure on `{0,1}^{E^*}`, including
coordinates with Dirac marginals, and it extends to events that depend on
infinitely many coordinates by martingale convergence. So any two such
events are positively correlated under every `P_F`.

## 2. The bisector split

Write `d(z, U) = min_{u in U} |z - u|`, with Euclidean distance. Define

```text
L = { e^* : d(m(e), U^-) < d(m(e), U^+) },     R = { e^* : d(m(e), U^+) < d(m(e), U^-) }.
```

These are disjoint. Dual edges at equal distance lie in neither.

**Lemma 2.1.** Every `e^*` with `e in S^+` lies in `R`, and every `e^*` with
`e in S^-` lies in `L`.

*Proof.* Let `e in S^+`. Both endpoints of `e` are in `U^+`, so
`d(m(e), U^+) = 1/2`. Every lattice point other than the two endpoints of
`e` is at distance at least `sqrt 5 / 2` from `m(e)`. The path's vertices are
distinct, so `U^-` does not contain the endpoints of `e`, and
`d(m(e), U^-) >= sqrt 5/2 > 1/2`. The case `e in S^-` is symmetric. `□`

**Lemma 2.2 (leaving `L` costs distance).** Let `x in U^-` and let `gamma`
be a dual circuit surrounding `x` that is not contained in `L`. Then
`gamma` contains a point at distance at least `delta(x)/2` from `x`, where
`delta(x) = d(x, U^+)`. The same holds with `L`, `U^-`, `U^+` replaced by
`R`, `U^+`, `U^-`.

*Proof.* Take an edge `f^*` of `gamma` not in `L`, and let `m` be its
midpoint. Then `d(m, U^+) <= d(m, U^-) <= |m - x|`, since `x in U^-`. So
`delta(x) <= |x - m| + d(m, U^+) <= 2 |x - m|`. `□`

## 3. Proof of Theorem 1

Consider these events, each an event about dual-open circuits:

* `A = {no dual-open circuit surrounds a vertex of V(S^-)}`;
* `B = {no dual-open circuit surrounds a vertex of V(S^+)}`;
* `A^L = {no dual-open circuit with all its edges in L surrounds a vertex of V(S^-)}`;
* `B^R = {no dual-open circuit with all its edges in R surrounds a vertex of V(S^+)}`;
* `D^- = {no dual-open circuit not contained in L surrounds a vertex of V(S^-)}`;
* `D^+ = {no dual-open circuit not contained in R surrounds a vertex of V(S^+)}`.

By (1.1), `q(S) = P_S(A ∩ B)`, `q(S^-) = P_{S^-}(A)` and
`q(S^+) = P_{S^+}(B)`.

**Step 1 (drop to the half-planes).** `A ⊆ A^L` and `B ⊆ B^R`, so
`q(S) <= P_S(A^L ∩ B^R)`. The event `A^L` depends only on the dual edges
in `L`, and `B^R` only on those in `R`. Since `L ∩ R = ∅` and `P_S` is a
product measure,

```text
q(S) <= P_S(A^L) P_S(B^R).
```

**Step 2 (the half-plane event does not see the other pattern).** By Lemma
2.1, `L` contains no dual of an `S^+` edge. So the marginal of `P_S` on
`L` equals the marginal of `P_{S^-}` on `L`, and `P_S(A^L) = P_{S^-}(A^L)`.
Likewise `P_S(B^R) = P_{S^+}(B^R)`.

**Step 3 (Harris back to the one-sided event).** Under `P_{S^-}`,
`A = A^L ∩ D^-`, and both events are decreasing. By Harris,

```text
q(S^-) = P_{S^-}(A) >= P_{S^-}(A^L) P_{S^-}(D^-).
```

Similarly `q(S^+) >= P_{S^+}(B^R) P_{S^+}(D^+)`. Combining Steps 1-3,

```text
q(S) <= q(S^-) q(S^+) / ( Theta^- Theta^+ ),   Theta^- = P_{S^-}(D^-),  Theta^+ = P_{S^+}(D^+).   (3.1)
```

**Step 4 (lower bound on `Theta`).** For `x in V(S^-)`, let `D_x` be the
event that no dual-open circuit which is not contained in `L` surrounds
`x`. Then `D^- = ∩_x D_x`, a finite intersection of decreasing events, and
Harris gives `Theta^- >= prod_x P_{S^-}(D_x)`. Each `D_x` is decreasing, and
`P_{S^-}` makes fewer dual edges open than the free measure `P_∅`. So:

* `P_{S^-}(D_x) >= P_∅(no dual-open circuit surrounds x) = P(x in an infinite cluster of omega) = theta`,
  by Lemma 1.1 with `W = {x}`;
* by Lemma 2.2, `D_x^c` requires a dual-open circuit surrounding `x` with a
  point at distance `>= delta(x)/2` from `x`. So
  `P_{S^-}(D_x) >= 1 - psi(delta(x)/2)`, by translation invariance of `P_∅`.

Hence `Theta^- >= prod_{x in V(S^-)} max(theta, 1 - psi(delta(x)/2))`. The
same holds for `Theta^+`. With (0.1) and (3.1) this is Theorem 1. Since
each factor is at most `1`, extending the product to all path vertices only
weakens the bound, and this gives the stated bound on `log K_n`. `□`

## 4. The dual circuit tail

`psi(rho) -> 0` exponentially. A dual circuit `gamma` surrounding `0`
crosses the positive horizontal half-axis. It therefore contains a dual
vertex `v_t = (t + 1/2, 1/2)` or `(t + 1/2, -1/2)` for some integer `t >= 0`.
It also crosses the negative half-axis, at distance at least `t + 1` from
`v_t`. If it has a point at distance `>= rho` from `0`, that point is at
distance at least `rho - t - 1` from `v_t`. Let
`phi(s) = P_{1-p'}(a given dual vertex is joined by a dual-open path to distance >= s)`.
Then

```text
psi(rho) <= 2 sum_{t >= 0} phi( max(t + 1, rho - t - 1) ).
```

The dual is Bernoulli(`1-p'`) on a copy of `Z^2` with `1-p' < 1/2 = p_c`.
By sharpness (Kesten 1980 for `p_c = 1/2`; Menshikov 1986;
Aizenman--Barsky 1987; Duminil-Copin--Tassion 2016),
`phi(s) <= C e^{-c s}`. Splitting the sum at `t = rho/2` gives
`psi(rho) <= C (1 + rho) e^{-c rho/2} <= C_1 e^{-c_1 rho}`.

## 5. Corollaries

**Corollary 2.** On a monotone lattice path, the `l1` distance between
`x_a` and `x_b` is `|a-b|`, and Euclidean distance is at least `l1/sqrt 2`.
Distinct vertices at `l1` distance `1` are consecutive, so the path is
chordless. For `x_{k-j} in U^-` with `j >= 1`,
`delta(x_{k-j}) >= min_{i >= 0} (j+i)/sqrt 2 = j/sqrt 2`. For
`x_{k-1+j} in U^+` with `j >= 1`, `delta >= j/sqrt 2`. Each side has at
most one vertex for each `j`, and each factor is at most `1`. So

```text
Theta^± >= prod_{j >= 1} max(theta, 1 - psi(j/(2 sqrt 2))),
```

which is positive: every factor is at least `theta > 0`, and
`sum_j psi(j/(2 sqrt 2)) < infinity` by Section 4, so all but finitely many
factors are at least `1/2` and the product converges. Theorem 1 of
`fpbs-path-bridge-ratio-untilted-coverage-decorrelation` (for every
environment, `Br/TJT <= K_n` and `D_n >= (1-2/n)/K_n`) then gives the
stated consequences. `□`

**Corollary 3.** For `delta(x) <= rho_0`, bound the factor below by
`theta`. For `delta(x) > rho_0` we have `psi(delta(x)/2) <= 1/2`, and
`-log(1-y) <= 2y` for `y in [0,1/2]`. `□`

**Box targets.** Replace "infinite cluster" by "cluster meeting `∂B`". Lemma
1.1 becomes: `W` does not meet `∂B` in `eta ∩ E(B)` iff a dual-open circuit
inside `B` surrounds a vertex of `W`. Steps 1-4 are unchanged, and `psi`
only decreases when circuits are restricted to lie in `B`.

**Other planar lattices.** Sections 1-3 use only three facts: planar
duality in the form of Lemma 1.1, the product structure of the dual
measure, and the metric inequality of Lemma 2.2. Lemma 2.2 holds in any
metric, and Lemma 2.1 needs only that an edge's midpoint is strictly closer
to its endpoints than to other vertices. Lemma 1.1 holds whenever dual-open
clusters are a.s. finite, which is the case for `p' > p_u = 1 - p_c(G^*)` on
a quasi-transitive nonamenable planar lattice (Benjamini--Schramm 2001).
Section 4 then follows from sharpness on the dual.

## 6. Where the constant is lost

The loss is entirely in Step 4, which pays `1/theta` for each vertex within
`rho_0` of the cut. The circuits that leave `L` around different vertices
near the cut are nested, or they cross the same few dual edges near
`m(e_k)`. So `D^-` should cost `O(1/theta)` in total, not a product. A proof
of that would give `K <= C/theta` on geodesic paths. It needs a
decomposition of `D^-` by the outermost exiting circuit, not Harris applied
vertex by vertex.
