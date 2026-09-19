---
rg: 2
id: fpbs-bisector-chain-is-polynomial-in-inverse-theta-proof
kind: route
title: The declared pattern only removes dual edges and V(S^-) lies in the negative axis, so Theta^- >= P(D^-(axis)); blocks of the dual-open graph decide D^- exactly; one primal-open circuit per dyadic scale in the left half-plane, around a dyadic stretch of the axis, with consecutive circuits forced to cross, traps every dual circuit around the axis inside L, at one RSW constant per scale up to L(p')
target: fpbs-bisector-chain-is-polynomial-in-inverse-theta
requires:
  - fpbs-planar-spine-multirun-decorrelation-by-dual-circuits
  - fpbs-bisector-split-chain-caps-at-inverse-theta-squared
---

Notation as in the target, in
`fpbs-bisector-split-chain-caps-at-inverse-theta-squared-proof`, and in
`fpbs-planar-spine-multirun-decorrelation-by-dual-circuits-proof`, whose
Steps 1-3 (the chain `K <= 1/(Theta^- Theta^+)`) we use. A *dual circuit*
is a cycle of the dual lattice, viewed as a Jordan curve through dual
vertices. A dual edge crosses exactly one primal edge and meets no primal
vertex. So a dual-open circuit is disjoint, as a subset of `R^2`, from
every primal-open edge and from every primal vertex. `int(C)` and `ext(C)`
denote the bounded and unbounded components of `R^2 \ C`. `U^-_∞` is the
full ray `{(a,0) : a <= 0}`, and `D^-(W)` is as in the target.

## 1. Theorem 1 (pattern-free reduction)

`D^-(W)` is the complement of the event that some dual-open circuit with
an edge outside `L` surrounds a vertex of `W`. That bad event is
increasing in the set of dual-open edges. So `D^-(W)` is increasing in the
primal configuration, and it shrinks as `W` grows.

The measure `P_{S^-}` declares the edges of `S^-` primal-open and leaves
the other edges i.i.d. It therefore stochastically dominates `P`. The
vertex set `V(S^-)` lies in `U^-` (the path vertices on the `U^-` side of
the cut), and `U^-` lies in `U^-_∞`. Hence

```text
Theta^-(S) = P_{S^-}(D^-(V(S^-))) >= P_{S^-}(D^-(U^-_∞)) >= P(D^-(U^-_∞)) =: Phi^- .
```

The reflection `(x,y) -> (1-x, y)` maps `L` onto `R` and `U^-_∞` onto
`U^+_∞`, and it preserves `P`, so `Phi^+ = Phi^-`. Inserting this into the
chain gives `K(S) <= 1/(Phi^-)^2`. The bound holds for every pattern,
every split and every path length. On a box proxy (target `∂B`, dual edges
restricted to those crossing edges of `B`), the same argument gives the
same bound with the proxy `Phi^-_B`, which decreases to `Phi^-` as `B`
grows. `∎`

## 2. Theorem 2 (blocks decide `D^-`)

**Lemma 2.1.** Let `H` be a finite 2-connected plane graph, let `e` be an
edge of `H`, and let `f` be a bounded face of `H`. Then some cycle of `H`
passes through `e` and surrounds `f`.

*Proof.* Since `H` is 2-connected, the boundary of its unbounded face is a
cycle `C_0`, and every bounded face lies in `int(C_0)`. If `e ∈ C_0`, take
`C_0`.

Otherwise let `e = uv`. The sets `{u,v}` and `V(C_0)` both have at least
two elements, so by Menger's theorem there are two vertex-disjoint paths
`P_u` from `u` to `x ∈ C_0` and `P_v` from `v` to `y ∈ C_0`, internally
disjoint from `C_0`, with `x ≠ y`. (A path is trivial if its start already
lies on `C_0`.) Then `Q = P_u^{-1} e P_v` is a path from `x` to `y` that
lies in the closed disk bounded by `C_0` and meets `C_0` only at `x` and
`y`. So `C_0 ∪ Q` is a theta graph. It divides `int(C_0)` into the
interiors of `C_1 = Q ∪ C_0[x,y]` and `C_2 = Q ∪ C_0[y,x]`, and the rest of
`int(C_0)` is `Q` itself.

The face `f` is connected, lies in `int(C_0)`, and is disjoint from
`Q ⊆ H`. So `f ⊆ int(C_1)` or `f ⊆ int(C_2)`. Both `C_1` and `C_2` contain
`e`. `∎`

**Proof of Theorem 2.** Let `G_N` be the union of the blocks of the
dual-open graph (in a fixed finite box) that contain an edge not in `L`.

*If `v` lies in a bounded face of `G_N`:* the boundary of a bounded face
of a plane graph contains a cycle `C` with `v ∈ int(C)`. A cycle lies in a
single block `B` of `G_N`. This `B` contains a non-`L` edge `e`, and `v`
lies in a bounded face `f` of `B` (a face of `B` inside `C`). By
Lemma 2.1, a cycle of `B` through `e` surrounds `f ∋ v`. It is a
dual-open circuit not contained in `L`.

*Conversely:* suppose a dual-open circuit `C` with a non-`L` edge `e`
surrounds `v`. Then `C` lies in one block, and that block contains `e`, so
`C ⊆ G_N`. Since `v` is a primal vertex it is not on `G_N`, and
`v ∈ int(C)` lies in a bounded face of `G_N`. `∎`

**Algorithm.** Faces of any subgraph of the dual lattice are unions of the
closed unit squares centred at primal vertices. Two primal vertices joined
by a primal edge `g` lie in the same face of `G_N` if and only if the dual
edge `g*` is not in `G_N`. So the vertices in the unbounded face are
exactly those reached from `∂B` by a flood over primal edges `g` with
`g* ∉ G_N`. `D^-(U^- ∩ B)` holds if and only if the flood reaches every
negative-axis vertex of `B`.

`theta_chain.c` implements this. It uses an iterative Tarjan block
decomposition with an edge stack, marks every edge of a block that
contains a non-`L` edge, and then floods. With a declared pattern the dual
edges of the pattern are removed first, and only `V(S^-)` is tested. For
the single-edge pattern `{(-1,0)(0,0)}`, Theorem A of the w13 node says
that `D^-` equals the run reaching `∂B`. The test reproduced this on every
sample: 0 mismatches in 3000 samples at `n = 8` and 1000 at `n = 20`.

## 3. Theorem 3 (nested left circuits)

**Black boxes.** We use three standard facts.

* (RSW) For each `rho >= 1` there is `c(rho) > 0` such that, for all
  `m >= 2` and all `p' >= 1/2`, a `(rho m) × m` rectangle has a primal-open
  crossing in the long direction with probability at least `c(rho)`. At
  `p' = 1/2` this is RSW for bond percolation on `Z^2`, and it extends to
  `p' > 1/2` by monotonicity. No near-critical input is needed here.
* (Kesten, exponential decay beyond `L`) For `p' > 1/2` the dual is
  subcritical, and `P(x <->* y) <= exp(-c|x-y|/L(p'))`.
* (Kesten, scaling relation) `theta(p') ≍ pi_{1/2}(L(p'))`, and
  `pi_{1/2}(n) <= C n^{-alpha}` for some `alpha > 0`.

**The circuits.** For `k >= 5` put `s = 2^k` and

```text
I_k = [-2s, -s/4] × [-s/16, s/16],     O_k = [-2s - s/16, -3s/16] × [-s/8, s/8].
```

Let `G_k` be the event that the closed region `O_k \ int(I_k)` contains a
primal-open circuit `Lambda_k` surrounding `I_k`. The region is the union
of four rectangles:

* top and bottom, each `[-2s - s/16, -3s/16] × ±[s/16, s/8]`, with aspect
  ratio 30;
* left and right, each `[-2s-s/16, -2s] × [-s/8, s/8]` and
  `[-s/4, -3s/16] × [-s/8, s/8]`, with aspect ratio 4.

Suppose each of the four has a long-direction crossing. Adjacent crossings
meet in the corner squares, because a left-right and a top-bottom crossing
of a square share a vertex. The union of the four crossings then contains
a circuit around `I_k`. By FKG, `P(G_k) >= c_1 := c(30)^2 c(4)^2` for every
`k` and every `p' >= 1/2`.

For large `k`, `G_k` fails only if some rectangle has a dual crossing in
the short direction, of length at least `s/16`. There are at most `C s`
starting points, so

```text
1 - P(G_k) <= C 2^k exp(-c 2^k / L).
```

Let `G_*` be the event that the 32 axis edges between `(0,0)` and
`(-32,0)` are all open. Then `P(G_*) = p'^{32} >= 2^{-32}`.

**Consecutive circuits cross.** Take `k >= 5` and `s = 2^k`, so that
`I_{k+1} = [-4s, -s/2] × [-s/8, s/8]` and
`O_{k+1} = [-4s - s/8, -3s/8] × [-s/4, s/4]`. Every point of `int(I_j)` lies
in `int(Lambda_j)`, and `int(Lambda_j)` lies in `O_j`. Three test points
settle the relative position of `Lambda_k` and `Lambda_{k+1}`:

* `(-s, 0)` lies in `int(I_k) ∩ int(I_{k+1})`, so it is inside both
  circuits;
* `(-3s, 0)` lies in `int(I_{k+1})` and outside `O_k`, so it is inside
  `Lambda_{k+1}` and outside `Lambda_k`;
* `(-0.3 s, 0)` lies in `int(I_k)` and outside `O_{k+1}`, since
  `-0.3 > -3/8`, so it is inside `Lambda_k` and outside `Lambda_{k+1}`.

Two disjoint Jordan curves are either nested or have disjoint interiors.
The three points exclude all three cases, so `Lambda_k` and `Lambda_{k+1}`
meet. Being lattice cycles, they share a vertex.

The axis segment of `G_*` runs from `(0,0)`, which lies outside `O_5`
(`O_5` has `x <= -6`), to `(-32,0) ∈ int(I_5)`. So it meets `Lambda_5`.

**Coverage of the axis.** The open intervals `(-2^{k+1}, -2^{k-2})` for
`k >= 5` overlap in consecutive pairs, and their union is `(-∞, -8)`. So
every `(a,0)` with `a < -8` lies in `int(I_k)`, and hence in
`int(Lambda_k)`, for some `k`. Every `(a,0)` with `-32 <= a <= 0` lies on
the segment of `G_*`.

**Trapping.** On `G := G_* ∩ ∩_{k>=5} G_k`, let `P` be the union of the
`G_*` segment and all the `Lambda_k`. It is connected and unbounded, and it
consists of primal-open edges.

Let `C` be a dual-open circuit around some `v = (a,0)` with `a <= 0`. Then
`C` is disjoint from `P`. Since `P` is connected and unbounded, it lies in
`ext(C)`. That rules out `v ∈ P`, so `a < -8` and `v ∈ int(Lambda_k)` for
some `k`.

Now `int(C)` is connected, contains `v`, and misses `Lambda_k ⊆ ext(C)`.
Hence `int(C) ⊆ int(Lambda_k)`. Taking closures,
`C ⊆ int(Lambda_k) ∪ Lambda_k`, and `C ∩ Lambda_k = ∅` gives
`C ⊆ int(Lambda_k) ⊆ O_k ⊆ {x <= -3s/16}`. Every dual edge of `C` therefore
has a midpoint with negative first coordinate, so `C ⊆ L`. This proves
`G ⊆ D^-(U^-_∞)`.

**Counting.** All the events are increasing. By FKG applied to finite
intersections, and then continuity,

```text
Phi^- >= P(G) >= 2^{-32} · c_1^{#{k >= 5 : 2^k <= M L}} · prod_{2^k > M L} (1 - C 2^k e^{-c 2^k/L}).
```

Choose the constant `M` so that every factor of the last product is at
least `1 - (1/2)^{2^k/(ML)}`. The last product is then bounded below by an
absolute constant. So

```text
Phi^- >= c L^{-kappa},   kappa = log_2(1/c_1) .
```

By Theorem 1, `K(S) <= c^{-2} L^{2 kappa}`. By the scaling relation,
`L <= C theta^{-1/alpha}`, which gives `K(S) <= C' theta^{-2 kappa/alpha}`.
This holds for every pattern, split and path length on the straight path.
`∎`

**Remark (why the RSW constant cannot reach the gate).** The gate needs
`Phi >= theta^{gamma/2}` with `gamma < 36/5`, that is `Phi >= L^{-3/8}`
at the triangular-lattice exponents. The construction above pays
`log_2(1/c_1)` per scale, and even the one-arm cost alone is `5/48` per
scale. Any proof of the gate from Theorem 1 must therefore control the
*exact* exponent of `D^-(U^-_∞)`. Numerically that exponent is between 0.24
(the fit over `n = 16..256`) and 0.31(5) (the last local slope); see the
claim node. So the gate appears to hold, with modest room, but not by
constant counting.
The event looks conformally invariant: in the scaling limit it says that
no CLE_6 loop surrounding a point of the negative axis meets the right
half-plane. An SLE computation of its exponent on the triangular lattice
is the natural rigorous route.
