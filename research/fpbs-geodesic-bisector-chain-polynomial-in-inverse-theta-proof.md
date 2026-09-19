---
rg: 2
id: fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta-proof
kind: route
title: On a monotone path, boxes of half-width t/8 around path vertices at path distance t from the cut lie in the bisector half, so 64 linked primal circuits per dyadic scale plus an escape trap every dual circuit around U^- inside L (exponent polynomial in 1/theta); dual bridges and cut vertices of the wired cluster make the box event a face condition of edge and diagonal walls (linear-time test); FKG gluing of the box event, an RSW circuit and a no-large-dual-circuit event reduces the gate exactly to P_{1/2}(D_n) >= pi(n)^beta with beta < 18/5
target: fpbs-geodesic-bisector-chain-polynomial-in-inverse-theta
requires:
  - fpbs-bisector-chain-is-polynomial-in-inverse-theta
  - fpbs-planar-spine-multirun-decorrelation-by-dual-circuits
---

Notation as in the target and in
`fpbs-planar-spine-multirun-decorrelation-by-dual-circuits-proof` (the w12
chain) and `fpbs-bisector-chain-is-polynomial-in-inverse-theta-proof` (w14,
Theorems 1-3). `Box(x, r) = x + [-r, r]^2`. A *circuit* is a lattice cycle,
viewed as a Jordan curve; `int` and `ext` are its bounded and unbounded
complementary components. Primal-open edges and dual-open edges are
disjoint as subsets of `R^2` (a dual edge meets only its own primal edge,
which is closed). Two lattice paths of `Z^2` that meet as curves share a
vertex.

## 1. Theorem A (geodesic paths)

**Setting.** `x_0 ... x_n` is a geodesic path of `Z^2`: its `l^1` length
between any two of its vertices equals the index difference,
`|x_i - x_j|_1 = |i - j|`. (Equivalently, both coordinates are monotone.)
Split at `e_k`; `U^- = {x_0,...,x_{k-1}}`, `U^+ = {x_k,...,x_n}`; `L`, `R`,
`D^-`, `Theta^-` as in w12 Section 2-3, and

```text
Phi^-_gamma,k = P( no dual-open circuit not contained in L surrounds a vertex of U^- ) .
```

For `x_i in U^-` put `t(x_i) = k - i`, the path distance to the cut.

**Lemma A.1 (bisector room).** If `x_c in U^-`, `t(x_c) >= 2^j`, and
`rho = 2^{j-3}`, then every point `z in Box(x_c, rho)` satisfies
`d(z, U^-) < d(z, U^+)`. So every dual edge with midpoint in
`Box(x_c, rho)` is in `L`.

*Proof.* For `m >= k`, `|x_c - x_m|_2 >= |x_c - x_m|_1 / sqrt 2 = (m - c)/sqrt 2 >= t(x_c)/sqrt 2`.
And `|z - x_c|_2 <= sqrt 2 rho`. Hence
`d(z, U^-) <= sqrt 2 rho = 0.177 · 2^j`, while
`d(z, U^+) >= 2^j/sqrt 2 - sqrt 2 rho >= 0.530 · 2^j`. `□`

**Lemma A.2 (Theorem 1 of w14 on any path).** `Theta^-(S) >= Phi^-_gamma,k`
for every pattern `S`, and likewise on the `+` side. So
`K(S) <= 1 / (Phi^-_gamma,k Phi^+_gamma,k)`.

*Proof.* Verbatim w14 Theorem 1: `V(S^-) ⊆ U^-`, the event shrinks as the
vertex set grows, it is increasing in the primal configuration, and
`P_{S^-}` dominates `P`. The chain `K <= 1/(Theta^- Theta^+)` is w12
(3.1), which holds on every path with distinct vertices. `□`

**Construction.** Fix `k` and write `y = x_{k-1}`. The events below are
all increasing.

* `G_*`: the path edges `e_i` with `max(1, k-1023) <= i <= k-1` are all
  open. Probability at least `p'^{1023} >= 2^{-1023}`. Its edges form a
  path containing every `x_i` with `t(x_i) <= 1024`.
* *Chain centres.* For `j >= 10` and `0 <= l < 64` let
  `t_{j,l} = 2^j + l 2^{j-6}`. The centres are the vertices `x_c` with
  `t(x_c) = t_{j,l} <= k`, ordered by increasing `t`, with radius
  `rho_j = 2^{j-3}`. Consecutive centres are at index distance at most
  `2^{j-6} = rho_j/8`, where `j` is the scale of the nearer one, and the
  radius at most doubles from one centre to the next.
* `C_c`: `Box(x_c, rho) \ int Box(x_c, rho/2)` contains an open circuit
  `Lambda_c` surrounding `Box(x_c, rho/2)`. It is implied by long-way
  crossings of four `2rho × rho/2` rectangles, so
  `P(C_c) >= c(4)^4` by RSW and FKG.
* `R_c` (link to the next centre `x_b`): the rectangle
  `x_c + [0, 3 rho] × [-rho/8, rho/8]` has an open left-right crossing
  `pi_c`. `P(R_c) >= c(12)`.
* *Escape.* Let `x_*` be the last centre and `rho_* = rho` its radius, if
  `k > 1024`. If `k <= 1024`, put `x_* = y`, `rho_* = 2048`, and replace
  `C_*` by: `Box(y, 2048) \ int Box(y, 1024)` contains an open circuit
  `Lambda_*` surrounding `Box(y, 1024)`, and the `2048` horizontal edges
  to the right of `y` are open (probability bounded below by an absolute
  constant). For `m >= 1`, `E_m`: the square annulus
  `Box(x_*, 2^{m+1} rho_*) \ int Box(x_*, 2^m rho_*)` has an open circuit
  `Gamma_m` surrounding `Box(x_*, 2^m rho_*)`, and the annulus
  `Box(x_*, 2^{m+1} rho_*) \ int Box(x_*, 2^{m-2} rho_*)` has an open path
  `sigma_m` joining its two boundaries. `P(E_m) >= c(4)^5`.

Let `G` be the intersection of all these events.

**Lemma A.3 (connectivity).** On `G`, the union `P` of the `G_*` path, the
`Lambda_c`, the `pi_c`, `Lambda_*` (with its horizontal segment when
`k <= 1024`), the `Gamma_m` and the `sigma_m` is a connected, unbounded
set of primal-open edges.

*Proof.* *`G_*` meets the first circuit.* The first centre `x_c` has
`t = 1024`, so `x_c` lies on the `G_*` path, inside `Lambda_c`. The vertex
`y` is also on it, and `|x_c - y|_inf >= |x_c - y|_1 / 2 = 1023/2 > rho = 128`,
so `y` is outside `Box(x_c, rho) ⊇ Lambda_c ∪ int Lambda_c`. The path joins
an interior point to an exterior point, so it meets `Lambda_c`.

*Consecutive circuits are linked by `pi_c`.* Let `x_b` follow `x_c`, with
radii `rho_c` and `rho_b in {rho_c, 2 rho_c}`, and `|x_b - x_c|_inf <= rho_c/8`.
The left side of the `R_c` rectangle lies in `Box(x_c, rho_c/8)`, and
`Box(x_c, rho_c/8) ⊆ Box(x_b, rho_c/4) ⊆ int Box(x_b, rho_b/2)`, so it is inside
both `Lambda_c` and `Lambda_b`. The right side is at `l^inf` distance
`3 rho_c` from `x_c`. Both circuits and their interiors lie in
`Box(x_b, rho_b) ⊆ Box(x_c, rho_c/8 + 2 rho_c)`, strictly inside `Box(x_c, 3 rho_c)`.
So `pi_c` runs from inside to outside each circuit and meets both.

*The escape.* `sigma_1` starts on `∂Box(x_*, rho_*/2)`, which is contained in
`Lambda_* ∪ int Lambda_*` (`Lambda_*` surrounds that box; for `k <= 1024`,
`Lambda_*` surrounds `Box(y, 1024) ⊇ ∂Box(y, 1024)`), and ends on
`∂Box(x_*, 4 rho_*)`, which lies outside `Lambda_*` and in `Gamma_1 ∪ ext Gamma_1`. It starts inside
`Gamma_1`. So it meets both. In the same way, `sigma_m` meets
`Gamma_{m-1}` and `Gamma_m` for `m >= 2`. For `k <= 1024`, the horizontal
segment from `y` meets `Lambda_*` (it starts inside and ends on
`∂Box(y, 2048)`), and `y` lies on the `G_*` path. The `Gamma_m` leave every
bounded set. `□`

**Lemma A.4 (trapping).** `G ⊆ {no dual-open circuit not contained in L surrounds a vertex of U^-}`.

*Proof.* Let `C` be a dual-open circuit around `v = x_i in U^-`. `C` is
disjoint from `P`, and `P` is connected and unbounded, so `P ⊆ ext(C)`.
So `v notin P`, and in particular `t(v) > 1024`. Let `2^j <= t(v) < 2^{j+1}`.
Some centre `x_c` of scale `j` has `t_c <= t(v) < t_c + 2^{j-6}`. Then
`|v - x_c|_inf <= |v - x_c|_1 < rho_j/8`, so `v in int Lambda_c`. As in
w14, `int C` is connected, contains `v` and misses
`Lambda_c ⊆ P ⊆ ext(C)`, so `int C ⊆ int Lambda_c`, and hence
`C ⊆ int Lambda_c ⊆ Box(x_c, rho_j)`. By Lemma A.1 every edge of `C` is in
`L`. `□`

**Counting.** Every event above at spatial scale `r` (the chain at
`rho_j`, the escape at `2^m rho_*`) fails only if some rectangle of
bounded aspect and short side at least `r/8` has a dual-open crossing in
its short direction. So its failure probability is at most
`C r^2 exp(-c r / L(p'))`. There are 128 events per chain scale and one
`E_m` per escape scale. By FKG and continuity, exactly as in w14
Theorem 3,

```text
Phi^-_gamma,k  >=  2^{-1023} c_0 · (c(4)^4 c(12))^{64 J} · (c(4)^5)^{M'} · c_tail ,
```

where `J = #{j >= 10 : 2^j <= min(k, M L)}`, `M' = #{m >= 1 : 2^m rho_* <= M L}`,
and `c_tail > 0` bounds the product of the factors `1 - C r^2 e^{-c r/L}`
over the scales beyond `M L`. Both `J` and `M'` are at most
`log_2(M L) + 1`, so

```text
Phi^±_gamma,k >= c L(p')^{-kappa_1},    kappa_1 = 64 log_2(1/(c(4)^4 c(12))) + 5 log_2(1/c(4)) ,
```

uniformly over geodesic paths, lengths, split edges and `p' in (1/2, 1)`.
With Lemma A.2 and Kesten's scaling relation (as in w14),
`K(S) <= C L^{2 kappa_1} <= C' theta^{-2 kappa_1/alpha}`. `∎`

**Remarks.** (i) Only two facts about the path were used:
`d(x_c, U^+) >= t(x_c)/sqrt 2` and `|x_i - x_c| <= |i - c|`. For a
`lambda`-quasi-geodesic (`|x_i - x_j|_1 >= |i - j|/lambda`), take
`rho_j = 2^{j-3}/lambda` and `64 lambda` centres per scale; the exponent is
then `O(lambda)`. For hairpins `d(x, U^+)` is bounded along the fold and no
box of growing size fits, in line with
`fpbs-hairpin-paths-break-uniform-bridge-ratio`.
(ii) For the same reason as in w14's Remark, the exponent `kappa_1` is far
above the gate. Theorem A is the scope statement: on every geodesic path
the chain output is polynomial in `1/theta`, and the gate question reduces
to the exact exponent of `Phi^±_gamma,k`. Since `Phi^-` for a geodesic path
and a straight path are both governed by the same local picture near the
cut, the natural conjecture is that the straight path is the worst
geodesic up to constants (not proved).

## 2. Theorem B (the pinch-wall criterion for the straight-path event)

**Box model.** This is the model of w14's `theta_chain.c` and of
`phi_fast.c`. `B = [-n, n]^2`; the primal edges are those of `B`; the
dual vertices are the centres of the unit plaquettes `Q ⊆ B`; the dual
edges are the duals `e^*` of the edges `e` of `B` not contained in `∂B`.
`I` is the set of vertices joined to `∂B` by an open path of `B` (so
`∂B ⊆ I`: the boundary is wired). `L` is the set of dual edges with
midpoint abscissa `< 1/2`, and `D_n` is the event that no dual-open circuit
not contained in `L` surrounds a vertex `(a, 0)`, `-n < a <= 0`.

**Fact B.0.** A dual circuit is not contained in `L` iff it has a dual
vertex with abscissa `>= 1/2`. (A dual vertex at abscissa `>= 3/2` has
no `L` edge; one at `1/2` has exactly one, so a circuit through it uses a
non-`L` edge; and a non-`L` edge has an endpoint at abscissa `>= 1/2`.)

**Walls.** `W` is the union of the closed segments of the edges of `B`
with both endpoints in `I`, open or closed (*edge walls*), and of the
diagonals `uw` of plaquettes `Q ⊆ B` whose opposite corners `u, w` are both
in `I` (*pinch walls*). A *face* is a component of `int(B) \ W`. No wall
contains a lattice point outside `I`.

**Theorem B.** `D_n` fails iff some `v = (a, 0)`, `-n < a <= 0`, `v notin I`,
lies in a face that meets a plaquette with centre abscissa `>= 1/2`.

*Proof of "only if".* Let `C` be a dual-open circuit with a dual vertex
`q` at abscissa `>= 1/2` (Fact B.0), surrounding `v = (a,0)`. Every open
path from `v` to `∂B` crosses `C`, which is impossible, since it would
cross an edge whose dual is on `C` and hence closed. So `v notin I`, and the
same holds for every vertex in `int C`. Now `int C` meets no wall:

* an edge crossed by `C` has exactly one endpoint in `int C`, and that
  endpoint is not in `I`; an edge not crossed by `C` does not meet `C` and
  has both endpoints on one side; if both are in `int C`, neither is in `I`;
* `C` meets a plaquette `Q` only when it passes through the centre of `Q`.
  If the centre of `Q` is in `int C`, then `Q ⊆ int C` and no corner is in
  `I`. If `C` passes through the centre, it cuts `Q` along two
  half-dual-edges. When it goes straight, the two outside corners are
  adjacent, so no diagonal wall exists. When it turns, one corner is
  inside, and the only possible diagonal wall joins the two outside
  corners opposite each other. That diagonal meets the inside part of `Q`
  (a quarter square at the inside corner) only at the centre, which lies
  on `C`.

So `int C` lies in one face. It contains `v` and meets the plaquette
whose centre is `q`, on the inside of `C`. `□`

*Proof of "if".* Let `F` be the face of `v`, meeting a plaquette `Q_0`
with centre abscissa `>= 1/2`. Let `A` be the set of lattice vertices in
`F`. They are all outside `I`.

*(i) Local structure.* In a plaquette `Q`, look at the pieces of `Q \ W`.
A piece whose closure contains a corner `u notin I` contains a
neighbourhood of `u` in `Q`, because no wall comes near `u`. A piece whose
closure has only `I` corners is bounded entirely by walls inside `Q`. It
is the half of `Q` cut off by a diagonal wall when three corners are in `I`,
or a quarter when all four are. In particular, a face that contains a
vertex never contains such an isolated piece. So `Q_0 ∩ F` is a piece with
a corner `u_0 notin I` in `A`.

*(ii) `A` is 4-connected.* Within one plaquette, the corners in `A` that
belong to one piece are 4-connected through corners of that piece: two
opposite corners in one piece force the other diagonal to be absent, so a
third corner is not in `I` and is joined to both by non-wall sides.
Consecutive pieces along a path in `F` share a side that is not a wall,
or a corner. In either case they share a vertex not in `I`, which lies
in both pieces. So `A` is connected in the lattice.

*(iii) The outer boundary is dual-open.* Let `Sigma` be the union of the
closed dual squares `s(u) = u + [-1/2, 1/2]^2` for `u in A`. Its boundary
edges are the duals of the edges `uw` with `u in A` and `w notin A`. Such
an edge is closed, and `w in I`. Indeed, if `w notin I`, then the segment
`uw` is not a wall, and no other wall meets it except at its endpoints,
which are not in `I`. So `w in F`, and hence `w in A`. If `w in I`, the
edge is closed, since otherwise `u` would be joined to `∂B`. Such an edge
is not contained in `∂B`, because `u` is interior.

*(iv) Conclusion.* Since `A` is 4-connected, the boundary of the
unbounded component of `R^2 \ Sigma` is a dual circuit `C` that surrounds
`A`. This is the standard outer-boundary lemma for site clusters of `Z^2`:
a self-touching point would enclose a square of the unbounded component.
By (iii), `C` is dual-open, and it surrounds `v`. The point of `Sigma` with
the largest abscissa lies on `C`. Since `u_0` is a corner of a plaquette
with centre abscissa `>= 1/2`, `u_0` has abscissa `>= 0`, so `s(u_0)` reaches
abscissa `>= 1/2`. So `C` has a dual vertex at abscissa `>= 1/2`, and by
Fact B.0, `C ⊄ L`. `∎`

**Why pinch walls matter.** Without the diagonal walls the criterion
("the face of `I`-edges containing `v` reaches the right") overcounts
failures. A dangling dual fjord between two `I` pieces that touch
diagonally connects `v` to the right half-plane in the plane, but no dual
circuit can close through the touching point. On the samples in the
experiment, the wall criterion without pinches disagrees with the block
algorithm, and the criterion with pinches agrees on every sample.

**Algorithm (`phi_fast.c`).** Cut every plaquette into four triangles by
both diagonals. Flood the triangle adjacency graph from all triangles of
plaquettes with centre abscissa `>= 1/2`, crossing a plaquette side only
when it is not an edge wall and a half-diagonal only when that diagonal
is not a pinch wall. `D_n` fails iff some `v = (a,0) notin I`,
`-n < a <= 0`, has a reached triangle next to it (the code tests the
bottom triangle of the plaquette `[a, a+1] × [0, 1]`; all triangles around
`v` lie in the face of `v`). With `I` from one BFS, this is `O(n^2)` per
box. The nested boxes `n = N, N/2, ...` of one configuration are
evaluated on the same sample, and `D_{2n} ⊆ D_n` on each sample (a
circuit in `B_n` is a circuit in `B_{2n}`, and `I_{2n} ∩ B_n ⊆ I_n`, since a
path to `∂B_{2n}` hits `∂B_n` first). So the conditional ratios
`P(D_{2n} | D_n)` are measured sample by sample with low variance.

**Validation.** Per-sample outcomes of `phi_fast` and of w14's
block-decomposition code `theta_chain.c` (same generator, same seeds), at
`p = 1/2` with `1500` samples at each of `n = 4, 8, 16, 32`, with `300` at
`n = 64`, and with `1000` at `n = 24` at `p = 0.45` and at `p = 0.55`: `0`
mismatches. On all production runs there were `0` monotonicity violations
(`D_{2n}` true while `D_n` false).

## 3. The exponent of the pattern-free event: numerics and the exact missing statement

Theorem A gives some polynomial exponent, but a poor one: `kappa_1` is in
the thousands. The target needs a quantitative gate. By w14, Theorem 1,
`K <= Phi^{-2}`, and `theta(p') = L(p')^{-5/48 + o(1)}`. Suppose
`Phi(p') = L(p')^{-zeta + o(1)}`. Then `K <= theta^{-96 zeta/5 + o(1)}`, and
the gate `gamma < 36/5` is exactly `zeta < 3/8`. This section records what is
proved about `zeta`, what is measured, and the exact statement that
would close the gate.

### 3.1 Proved bounds

* **Lower bound on `zeta` (rigorous).** On `D^-` the origin is not
  surrounded by a dual-open circuit of `B_n` that exits `L`. Every dual
  circuit surrounding the origin has a dual vertex at abscissa `>= 1/2`,
  so it exits `L` (Fact B.0). Hence `D_n ⊆ {0 <-> ∂B_n}`, and
  `Phi_n(1/2) <= pi(n) = n^{-5/48 + o(1)}`, which gives `zeta >= 5/48`.
  The `PI` column below is `P(0 in I_n)`, the wired one-arm probability.
  It is measured on the same samples, and its local slopes sit at
  `≈ 0.10`, matching `5/48 = 0.104`. This is a calibration check of the
  pipeline.
* **Box proxy is an upper bound.** A dual circuit in the box model of
  `B_n` is a dual circuit of the plane. So `D ⊆ D_n` for the infinite-volume
  event, and `Phi(p') <= P_{p'}(D_n)` for every `n`.
* **Monotonicity.** `D_{2n} ⊆ D_n` on each sample (Section 2). So
  `Phi_{2^k n} = Phi_n · prod_i P(D_{2^{i+1} n} | D_{2^i n})`, and each
  conditional ratio is measured on the same samples.
* **Upper bound on `zeta`.** Only Theorem A's `kappa_1`. No elementary
  comparison with an arm event gives an exponent below `3/8`.
  - The natural candidate is "two open half-plane arms from the origin
    imply `D`" (exponent `1/3`). It is **false**: a vertex
    `v = (a,0)`, `a < 0`, can sit in a closed pocket below the axis that
    opens to the right under the arms' landing points. Then a dual circuit
    around `v` exits `L` without crossing either arm.
  - The event genuinely constrains every point of `U^- ∩ B_n`, not only
    the origin. That is why its exponent differs from every classical
    arm exponent.

### 3.2 Numerics (sharpened)

`phi_fast.c` (linear time, Section 2), validated sample by sample
against w14's `theta_chain.c` (0 mismatches). Critical bond percolation
on `Z^2`, `p = 1/2`, nested boxes `n = 8, ..., N` of one configuration.
There are two independent streams, A (`N = 1024`) and B (`N = 2048`).
The full output is in `results.txt`. Errors are 20-block jackknife. The
slope at `n` is `-log2 P(D_n | D_{n/2})`.

Pooled data: 5,900 samples to `n = 1024`, of which 1,100 go to
`n = 2048`. Stream A has 12 files and stream B has 11. There were 0
monotonicity violations.

| `n` | `Phi_n` | local slope of `Phi` | `P(0 in I_n)` | local slope of `PI` |
|---:|---:|---:|---:|---:|
| 8 | 0.689(6) | – | 0.758(6) | – |
| 16 | 0.595(7) | 0.211(11) | 0.707(6) | 0.101(6) |
| 32 | 0.500(7) | 0.251(8) | 0.657(6) | 0.106(6) |
| 64 | 0.415(6) | 0.268(10) | 0.609(5) | 0.108(5) |
| 128 | 0.351(7) | 0.243(15) | 0.566(6) | 0.107(5) |
| 256 | 0.293(6) | 0.258(15) | 0.529(6) | 0.098(9) |
| 512 | 0.245(4) | 0.262(14) | 0.493(6) | 0.100(6) |
| 1024 | 0.207(4) | 0.240(15) | 0.461(5) | 0.097(7) |
| 2048 (B only) | 0.197(11) | 0.169(23) | 0.460(14) | 0.078(19) |

At `n = 2048` the `Phi_n` column is not comparable with the rows above,
because stream B's `n = 8` value is `0.701`. The slope column is comparable.

**Reading.**

* The one-arm calibration slopes are `0.097-0.108`, against the exact
  `5/48 = 0.104`. The pipeline reproduces a known exponent to within
  about 5%.
* The `Phi` slopes show no upward drift from `n = 32` to `n = 2048`. Their
  weighted mean over `n = 64..2048` is `0.251(6)`. The global ratio from
  `n = 8` to `n = 1024` gives `zeta_eff = 0.248`.
* The ratio to the one-arm slope is `β_eff = 0.248/0.103 ≈ 2.4`, against
  the gate threshold `18/5 = 3.6`.
* The value `3/8` is excluded on every scale by more than 7 standard
  errors. Beyond `n = 2048` the statement is an extrapolation.
* The earlier estimate of w14, a last local slope of `0.31(5)` at
  `n = 256`, was a fluctuation. Here the same slope is `0.258(15)`.
* The "half" variant, which tests only `-n/2 < a <= 0`, agrees with `Phi`
  within errors at every scale. So the event is decided near the origin,
  not at the box boundary. This supports reading the slope as the exponent
  and not as a boundary effect.

### 3.3 Proposition C: the near-critical event is controlled by the critical box event

Notation:

* `Phi_n := P_{1/2}(D_n)` is the box event of Section 2.
* `Phi(p') := P_{p'}(D^-(U^-_∞))` is w14's `Phi^-` for the full ray
  `U^-_∞`, with `L` and `D^-` as in w14. Below, `U^-` means `U^-_∞`.
* `L(p')` is Kesten's correlation length, and
  `pi(n) := P_{1/2}(0 <-> ∂B_n)`.

**Proposition C.** There are absolute constants `c, C_0 > 0` such that,
for every `p' in (1/2, 1)`,

    Phi(p') >= c · Phi_{4 C_0 L(p')}.

*Proof.* Put `n = C_0 L(p')` and define three events.

* `D_{4n}` is the box event at scale `4n`.
* `G_n` is the event that some open primal circuit `Γ` lies in
  `B_{2n} \ B_n`.
* `F_n` is the event that no dual-open circuit `γ` surrounds a vertex
  `v = (a,0)` of `U^-` with `diam γ >= max(n, |a|)`.

All three events are increasing in the primal configuration, because
opening an edge closes its dual. So FKG and the monotone coupling give
`P_{p'}(D_{4n} ∩ G_n ∩ F_n) >= P_{1/2}(D_{4n}) · P_{1/2}(G_n) · P_{p'}(F_n)`.
By RSW, `P_{1/2}(G_n) >= c_1`. It remains to show two things: the
inclusion `D_{4n} ∩ G_n ∩ F_n ⊆ D^-`, and `P_{p'}(F_n) >= 1/2` once `C_0`
is large.

*Inclusion.* Let `γ` be a dual-open circuit that surrounds a vertex
`v = (a,0)` of `U^-` and is not contained in `L`. By Fact B.0, `γ` has a
dual vertex at abscissa `>= 1/2`. Also `γ ∩ Γ = ∅`, because dual-open and
primal-open edges are disjoint as sets. There are three cases.

1. `γ ⊂ int Γ ⊂ B_{2n}`. Then `γ` crosses only edges off `∂B_{4n}`, so it
   is a dual circuit of the box model of `B_{4n}`. It surrounds
   `v ∈ B_{2n}`, so `-4n < a <= 0`. This contradicts `D_{4n}`.
2. `Γ ⊂ int γ`. Then `γ` surrounds `0 ∈ U^-`, and
   `diam γ >= diam Γ >= 2n`. This contradicts `F_n`.
3. `int γ ∩ int Γ = ∅`. Then `v ∈ ext Γ`, so `a < -n`. Since `γ` surrounds
   `v` and reaches abscissa `1/2`, we get `diam γ > |a| > n`. This
   contradicts `F_n`.

*The event `F_n`.* Suppose `γ` violates `F_n`. Put `d = diam γ` and
choose `k` with `2^k <= d < 2^{k+1}`; then `2^{k+1} > n`.

* `γ` meets the axis to the left of `v` at a point `w = (b,0)` with
  `a - d <= b <= a`. Since `|a| <= d`, this gives `|b| <= 2d < 2^{k+2}`.
* Some grid point `x_j = (-j 2^{k-3}, 0)` with `0 <= j <= 32` lies within
  `2^{k-4}` of `w`.
* `γ` contains a point at distance `>= 2^{k-1}` from `w`. So `γ` contains
  a dual-open crossing of the annulus around `x_j` with inner half-width
  `2^{k-4}` and outer half-width `2^{k-2}`.

For `p' > 1/2` the dual is subcritical beyond the scale `L(p')`: a dual
crossing of an annulus with half-widths `r` and `4r` has
`P_{p'}`-probability at most `C_1 exp(-c_2 r / L(p'))` (Kesten 1987; see
Nolin, *Near-critical percolation in two dimensions*, 2008, Lemma 39).
Summing over the 33 grid points and over all `k` with `2^{k+1} > n`,

    P(F_n^c) <= Σ_{2^{k+1} > n} 33 · C_1 · exp(-c_2 2^{k-4} / L) <= C_3 exp(-c_4 n / L),

which is at most `1/2` for `C_0` large. Hence
`Phi(p') >= (c_1/2) · Phi_{4n}`. `∎`

**Corollary C.1 (the gate in lattice-intrinsic form).** Suppose that for
some `β < 18/5`

    (H)   Phi_n >= c · pi(n)^β   for all n.

Then `K(S) <= C θ(p')^{-2β}` for every pattern, split and path length on
the straight path. So `gamma = 2β < 36/5`, and the gate of the target
holds for the bisector chain.

*Proof.* Combine w14, Theorem 1, with Proposition C:
`K <= Phi(p')^{-2} <= C · Phi_{4 C_0 L}^{-2} <= C · pi(4 C_0 L)^{-2β}`.
Kesten's scaling relation gives `θ(p') ≍ pi(L(p'))`, and RSW gives
`pi(4 C_0 L) ≍ pi(L)`. `∎`

The quantitative gate is therefore now **one inequality of critical
percolation**, (H), about a single explicit event at `p = 1/2`. No
near-critical input remains open: Proposition C is rigorous.

* At the triangular-lattice exponents, (H) reads
  `zeta := lim -log Phi_n / log n < (18/5)(5/48) = 3/8`.
* On `Z^2` it is the intrinsic ratio statement
  `limsup log Phi_n / log pi(n) < 18/5`.
* Measured (§3.2): `Phi_n` decays with local slope `≈ 0.25` per doubling
  and `P(0 in I_n)` with slope `≈ 0.10`, so `β_eff ≈ 2.4`, against a
  threshold of `3.6`.

### 3.4 Continuum form (heuristic; not used above)

In the scaling limit on the triangular lattice, take the nested CLE_6 in
the unit disk, and let `E_ε` be the event that no loop of diameter
`>= ε` meets both the negative real axis and the imaginary axis.

* A loop that surrounds a point of the negative axis and meets
  `{Re z >= 0}` crosses the negative axis and meets `iR`.
* Conversely, a loop that crosses the negative axis surrounds a segment
  of it.

So `Phi_n ≈ P(E_{1/n}) = n^{-zeta + o(1)}`. By scale invariance, `zeta` is
minus the log-rate of the one-step transfer operator for "no bad loop at
scales in `[r, 2r]`" acting on the law of the configuration seen from the
corner.

This is a wedge-type exponent for the quarter-plane angle `π/2` between
the two rays. It is not a classical arm exponent, because the event
constrains every point of the negative axis and not only the tip.

* The measured value `0.25 ± 0.01` is consistent with the polychromatic
  two-arm value `1/4`. It is inconsistent with `5/48`, with the half-plane
  one-arm value `1/3` and with the backbone value `≈ 0.357`.
* A proof that `zeta = 1/4` would give `gamma = 24/5`.

An SLE_6 computation of this wedge exponent, for example through a
radial or chordal exploration from `0` along the negative axis with
locality, is the natural rigorous route to (H) on the triangular lattice.
On `Z^2` it would still need the usual universality input, or a direct
proof of the intrinsic form of (H).

### 3.5 What is and is not established

| Item | Status |
|---|---|
| Theorem A: `K <= C θ^{-2 kappa_1/alpha}` on monotone paths, uniform in pattern, split, length and `p'`; `λ`-quasi-geodesics give `O(λ)` in the exponent | **Proved** |
| Theorem B: pinch-wall face criterion for `D_n`; linear-time evaluator validated against the block algorithm | **Proved** |
| Proposition C and Corollary C.1: the gate reduces exactly to the critical inequality (H) | **Proved** |
| (H), equivalently `zeta < 3/8` | **Open.** Numerically `zeta ≈ 0.25` with no upward drift up to `n = 2048` |
| Continuum identification of `zeta` | Heuristic |
| Two open half-plane arms at `0` imply `D` | **False** (pocket counterexample, §3.1) |
| Hairpin (non-geodesic) paths | Not covered: Lemma A.1 fails, and w13's two-run patterns show a genuine loss |

