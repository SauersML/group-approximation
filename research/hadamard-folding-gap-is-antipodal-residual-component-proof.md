---
rg: 2
id: hadamard-folding-gap-is-antipodal-residual-component-proof
kind: route
title: Symmetrize the weighting, symmetrize a max flow, read folded min cuts as 2-SAT solutions of the skew-symmetric residual graph, and price the odd-walk LP with the constant length 2/K
target: hadamard-folding-gap-is-antipodal-residual-component
requires:
  - hadamard-gadget-deletion-ratio-window
---

Notation as in the target. `iota(x) = -x` on `Q`, extended by
`iota(s) = t`. The network `N(w, xi)` is the undirected graph `Q` with
capacity `w(e)` on each length-one edge, plus arcs `s -> p` for `p in S+`
and `p -> t` for `p in S-` of infinite capacity. Since `iota(S+) = S-`, the
map `iota` is an automorphism of `N` swapping `s` and `t` whenever `w` is
symmetric.

## Step 0: cuts and assignments

For `B` with `s in B`, `t notin B`, `cap(B)` is the capacity of arcs
leaving `B`. It is finite iff `S+ ⊂ B` and `S- ∩ B = ∅`, and then
`cap(B) = w(cut f_B)` for `f_B = +1` on `B ∩ Q`, `-1` elsewhere.

* So `M(w, xi) = min cap(B)` over all finite cuts (max-flow min-cut makes
  it the max-flow value `val`).
* `f_B` is folded iff `iota(B) = B^c`. A folded `f` with `f(chi_a) = xi_a`
  has `f(xi_a chi_a) = +1` (oddness), so `B_f = {f = +1} ∪ {s}` is finite.
  Hence `F(w, xi) = min cap(B)` over finite `B` with `iota(B) = B^c`, and
  `F >= M`.

## Step 1: symmetric weightings (item 1)

* For folded `f`, `f(-x) f(-y) = f(x) f(y)`, so `cut_f(-e) = cut_f(e)` and
  `w(cut f) = w^-(cut f) = w^s(cut f)`. Hence `F(w, xi) = F(w^s, xi)`.
* For relaxed `f`, the mirror `f~(x) = -f(-x)` has the same pins and
  `cut_{f~}(e) = cut_f(-e)`, so `M(w^-, xi) = M(w, xi)`.
* `M(., xi)` is a minimum of linear functions of `w`, hence concave, so
  `M(w^s, xi) >= (M(w, xi) + M(w^-, xi))/2 = M(w, xi)`.
* So replacing `w` by `w^s` keeps `E F` and does not lower `E M`; both
  maxima in the minimax identity are attained at symmetric `w`.

## Step 2: a symmetric max flow (item 2, first part)

Write a flow as an antisymmetric `phi(u, v) = -phi(v, u)` with
`phi(u, v) <= c(u, v)` and conservation off `{s, t}`.

* Put `phi'(u, v) = phi(iota v, iota u)`. Since `c(iota v, iota u) = c(u, v)`
  (symmetric `w`, and `iota` swaps the source and sink arcs), `phi'` is
  feasible. Conservation at `x` is conservation of `phi` at `iota x`. The
  net outflow of `phi'` at `s` equals the net inflow of `phi` at `t`, so
  `phi'` has the same value.
* `phi~ = (phi + phi')/2` is a maximum flow with `phi~' = phi~`.
* Residual capacities `r(u, v) = c(u, v) - phi~(u, v)` satisfy
  `r(iota v, iota u) = c(u, v) - phi~'(u, v) = r(u, v)`. So `G_phi~`, the
  graph of arcs with `r > 0`, is skew-symmetric: `u -> v` iff
  `iota v -> iota u`.

## Step 3: min cuts are closed sets

For any max flow `phi` and finite `B` (`s in B`, `t notin B`),
`cap(B) - val = sum over u in B, v notin B of r(u, v)`, because
`val = sum over u in B, v notin B of phi(u, v)`. Every term is `>= 0`. So
`B` is a min cut iff no residual arc leaves `B`, that is iff `B` is closed
under residual reachability. In particular every closed `B` containing
`s` is finite, because `t` is not reachable from `s`.

## Step 4: the 2-SAT criterion (item 2)

Let `G = G_phi~` from Step 2. By Steps 0 and 3, `F(w, xi) = M(w, xi)` iff
some `G`-closed `B` with `s in B` satisfies `iota(B) = B^c`.

* **Only if.** Let `B` be such a set and suppose `x` and `-x` lie in one
  strongly connected component. Exactly one of them lies in `B`, and `B` is
  closed, so it contains the other too. Contradiction.
* **If.** Suppose no `x in Q` shares a component with `-x`.
  * Let `R` be the set of vertices reachable from `s`. By skew-symmetry,
    `iota(R)` is the set of vertices that reach `t`. `R ∩ iota(R) = ∅`,
    since a vertex in both gives a path `s -> t`.
  * Let `W = V \ (R ∪ iota(R))`. It is `iota`-invariant, and `G[W]` is
    skew-symmetric with no vertex in the component of its antipode. The
    components of `G[W]` are components of `G`: a cycle through a vertex of
    `W` and a vertex of `R` would put that `W` vertex in `R` (as `R` is
    closed under successors), and likewise for `iota(R)` and predecessors.
  * By Aspvall-Plass-Tarjan (1979), `G[W]` read as a 2-SAT implication
    graph (literal `x`, negation `-x`) has a satisfying assignment: a set
    `B_W ⊂ W` with `iota(B_W) = W \ B_W`, closed under arcs inside `W`.
  * Put `B = R ∪ B_W`. Then `iota(B) = iota(R) ∪ (W \ B_W) = B^c`.
  * `B` is closed. Arcs from `R` stay in `R`. An arc from `B_W` goes into
    `W`, where it stays in `B_W`, or into `R ⊂ B`. It cannot go into
    `iota(R)`, because then its tail would reach `t` and lie in `iota(R)`.
* By Step 3, `B` is a min cut with `iota(B) = B^c`, so `F = M`.

The test holds for one symmetric max flow iff it holds for all of them,
since both sides are statements about `F` and `M`.

## Step 5: the odd-walk LP (item 3)

`L(w, xi) = min sum_e w(e) d(e)` over `d : edges -> [0, 1]` with
`sum_{e in P} d(e) >= 1` for every walk `P` from `S+` to `S-` and every
walk from some `x` to `-x`.

* **`L <= F`.** For a folded pinned `f`, let `d` be the indicator of
  `cut f`. Along a walk from `S+` (value `+1`) to `S-` (value `-1`), or from
  `x` to `-x` (values `f(x)` and `-f(x)`), `f` changes sign an odd number
  of times. So `d` is feasible, with cost `w(cut f)`.
* **`M <= L`.** Dropping the antipodal-walk constraints leaves the
  path-length LP of the `S+`-`S-` cut, whose value is the min cut `M`
  (max-flow min-cut; the path LP is the dual of path-packing).
* **`L <= 2/K`.** Take `d = 2/K` on every edge (it is at most `1`, since
  `K >= 2`). A walk has at least as many edges as the Hamming distance of
  its ends:
  * `d_H(x, -x) = K`;
  * for `a != b`, `d_H(chi_a, chi_b) = K/2`, because distinct characters
    are orthogonal, and `d_H(chi_a, -chi_b) = K - K/2 = K/2`;
  * so every pair `(xi_a chi_a, -xi_b chi_b)` is at distance `K/2`
    (`a != b`) or `K` (`a = b`).

  So every constrained walk has length at least `1` under `d`, and the cost
  is `2/K` because `w` has total mass `1`.
* Taking `E_xi` and the maximum over `w`, `K max_w E_xi L <= 2`.
* **Dual form.** By LP duality, `L` is the maximum fractional packing of
  constrained walks under capacities `w`, which is the natural odd-cycle
  packing bound on the signed quotient graph `Q/±` with a pin vertex. Every
  packed walk uses at least `K/2` units of capacity, which is where every
  such certificate dies.

## Step 6: consequences (item 4)

Let `w` be symmetric with `K E_xi F(w, xi) > 2`.

* **(a)** By Martinsson's cap, `K E_xi M(w, xi) <= K z_U <= 2 < K E F`. So
  `F(w, xi) > M(w, xi)` on a set of `xi` of positive probability. By
  Step 4, each such `xi` has a vertex in the component of its antipode,
  that is, a component `C` with `-C = C`. (A component meeting its image
  under `iota` equals it, since `iota` maps components to components.)
* **(b)** By Step 5, `K E (F - L) = K E F - K E L > 2 - K E L >= 0`.
* Item 1 says the maximum defining `R*(k)` is attained at a symmetric `w`.
  So if `R*(k) > 2`, such a `w` exists, and it is the optimal one.
* Item (a) uses only item 5 of `hadamard-gadget-deletion-ratio-window`
  (Martinsson Proposition 49(c)). Item (b) and items 1 to 3 are
  self-contained.
