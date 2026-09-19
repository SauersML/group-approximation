---
rg: 2
id: fpbs-box-event-quadrant-k-arm-reduction-proof
kind: route
title: Proof that two single-wedge K-arms of the pinch-closed wired cluster force the FPBS pinch-wall box events, that on the one-arm event the axis-to-axis box event equals the two-half-plane K-arm event (flipped-triangulation duality), with the FKG and reflection product bounds, the no-product-certificate obstruction for zeta(0) < 3/16, and triangular-lattice measurements
target: fpbs-box-event-quadrant-k-arm-reduction
requires:
  - fpbs-box-event-wedge-angle-law-refutes-restriction
  - fpbs-cle6-hull-wedge-event-is-not-the-box-event
---

## 0. Setting

Notation as in `fpbs-cle6-hull-wedge-event-is-not-the-box-event` and
`fpbs-box-event-wedge-angle-law-refutes-restriction`. Triangular site
percolation at `p = 1/2`, in axial coordinates `(i,j)` with position
`x = i + j/2` and `y = j sqrt(3)/2`. The unit steps are
`d_0..d_5 = (1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)`, in cyclic order.
The box is `B_n = {|j| <= n, |2i+j| <= 2n}`, and its boundary sites are
black (wired). `I_n` is the black cluster of `∂B_n`, and
`S_n = {(i,0) : -n < i <= 0}`.

A step `c -> c + d_k` between two sites of `B_n` is a *pinch* if both
common neighbours `c + d_{k-1}` and `c + d_{k+1}` lie in `I_n` or outside
`B_n`. For a set `Y` of sites, `D'_n(Y)` is the event that no path of
non-`I_n` sites of `B_n` without pinch steps joins a site of `S_n` to a
site of `Y`. The two cases used here are

* `D'_n(pi/2) = D'_n({x > 0})`, the event whose exponent (H) needs
  below `3/8` (it implies the circuit form `D_n` by
  `fpbs-cle6-hull-wedge-event-is-not-the-box-event`, Theorem 1(c));
* `D'_n(0) = D'_n({(i,0) : i >= 1})`, the axis-to-axis event.

**Jumps and K-paths.** For a site `a` and an index `k`, the *jump*
`a -> b = a + d_k + d_{k+1}` goes to the far corner of the rhombus
`a, u = a + d_k, b, v = a + d_{k+1}`. Its segment `[a,b]` is the long
diagonal of the rhombus, and it crosses the short diagonal, the lattice
edge `[u,v]`, at their common midpoint. A *K-path* is a sequence of sites
of `I_n` in which consecutive sites are adjacent or joined by a jump. Its
curve is the union of the corresponding edges and jump segments.

**Wedges.** Consider the closed regions
`UL = {y >= 0, x <= 0}`, `LL = {y <= 0, x <= 0}`, `UH = {y >= 0}` and
`LH = {y <= 0}`. For `W` one of these, `A_n(W)` is the event that the
origin lies in `I_n` and some K-path, all of whose sites lie in `W`,
joins the origin to a boundary site of `B_n`.

## 1. Monotonicity and symmetry

**Lemma 1.1.** Each `A_n(W)` is increasing in the black configuration.

*Proof.* `I_n` is increasing: adding black sites can only enlarge the
boundary cluster. The adjacency and jump relations of a K-path depend only
on membership in `I_n`, so a K-path in `W` for a configuration `omega` is
still one for every `omega' >= omega`. The same holds for the condition
`0 ∈ I_n`. ∎

**Lemma 1.2.** The map `R(i,j) = (i+j, -j)` is the reflection
`(x,y) -> (x,-y)`. It preserves the lattice, `B_n`, `∂B_n`, `S_n` and
the Bernoulli measure. It maps jumps to jumps, `UL` to `LL` and `UH` to
`LH`. Hence `P(A_n(UL)) = P(A_n(LL))` and `P(A_n(UH)) = P(A_n(LH))`.

*Proof.* `R` is linear. It fixes `d_0`, swaps `d_1` with `d_5` and `d_2`
with `d_4`, and fixes `d_3`, so it permutes the unit steps. It therefore
maps a rhombus `(a, a+d_k, a+d_k+d_{k+1}, a+d_{k+1})` to a rhombus, and a
jump to a jump. It preserves `|j|` and `2i+j`, and hence `B_n` and its
boundary. Moreover `x(R(i,j)) = i + j - j/2 = x(i,j)` and
`y(R(i,j)) = -y(i,j)`. ∎

## 2. Two wedge arms force the box events

**Lemma 2.1 (curves do not cross).** Let `P` be a path of non-`I_n`
sites without pinch steps, and let `G` be a K-path. Then the curves of
`P` and `G` are disjoint.

*Proof.* Two edges of the triangular lattice meet only at a common
endpoint. That endpoint would be a site both in `I_n` (on `G`) and not in
`I_n` (on `P`), which is impossible. Now let `[a,b]` be a jump segment of
`G` across the rhombus `a,u,b,v`. The segment lies in the closed rhombus,
and it meets the edges of the triangular lattice only at `a`, at `b`, and
at the midpoint of `[u,v]`. The first two are sites of `I_n`, so they are
not on `P`. The third lies on `P` only if `P` uses the step `u -> v` or
`v -> u`. The common neighbours of `u` and `v` are `a` and `b`, both in
`I_n`, so that step is a pinch, which `P` does not use. ∎

**Lemma 2.2 (crossing).** Let `Q` be a closed convex polygon, a
topological closed disk, whose boundary circle contains four distinct
points `p1, q1, p2, q2` in this cyclic order. A curve in `Q` from `p1`
to `p2` and a curve in `Q` from `q1` to `q2` intersect.

This is the standard consequence of the Jordan curve theorem, and it is
the same statement that underlies crossing duality for percolation in a
disk.

**Theorem 2.3.**
(a) `A_n(UL) ∩ A_n(LL) ⊆ D'_n(pi/2)`.
(b) `A_n(UH) ∩ A_n(LH) ⊆ D'_n(0)`.

*Proof of (a).* Assume both arm events hold, and suppose a pinch-free
path `P = (v_0, ..., v_m)` of non-`I_n` sites runs from `v_0 ∈ S_n` to
`v_m` with `x(v_m) > 0`. We derive a contradiction.

*Step 1: reduce to one half.* Take the last index `r` with `v_r` on the
real axis at `x <= 0`, and the first index `m' > r` with `x(v_{m'}) > 0`.
Unit steps change `j` by at most 1. A real-axis site with `x <= 0` is
either in `S_n`, or it is the boundary site `(-n,0)`, which lies in
`I_n` and so is not on `P`. Hence `v_r ∈ S_n`, and `v_r` is not the
origin because the origin lies in `I_n`. All of `v_{r+1},...,v_{m'-1}`
lie off the real axis and at `x <= 0`, so they lie on one side of it,
say `y > 0` (the other side is the mirror image under Lemma 1.2).
The site `v_{m'}` is a neighbour of a site with `j >= 1`, so `j(v_{m'}) >= 0`.
If `j(v_{m'}) = 0`, then `v_{m'}` is `(i,0)` with `i >= 1`. The
neighbours of such a site with `j = 1` are `(i,1)` and `(i-1,1)`, and both have
`x >= 1/2 > 0`. That contradicts the choice of `m'`. So `j(v_{m'}) >= 1`,
and the whole piece `P' = (v_r, ..., v_{m'})` stays in `y >= 0`. The
same holds when `m' = r+1`: the neighbours of a site `(i,0)` with
`i <= 0` all have `x <= i + 1`, so `x > 0` forces `i = 0`, the origin,
which is excluded.

*Step 2: the disk.* Let `Q = UL ∩ hull(B_n)`. It is a convex polygon.
Its boundary runs from the corner `0` along the negative real axis to
`(-n,0)`, then along `∂hull(B_n)` to the point `t*` where the top edge
meets the line `x = 0`, then down the positive imaginary axis to `0`.
(In the `(x,y)` plane `hull(B_n)` is the rectangle
`|x| <= n, |y| <= n sqrt(3)/2`.)
Cut the curve of `P'` at its first point `t` on the line `x = 0`. This
point exists because `x(v_r) <= 0 < x(v_{m'})`, and it has `y > 0`.
Before `t` the curve lies in the open region `{x < 0, y > 0}`, apart from
its start `s = v_r`, which lies on the segment `(-n, 0)` of the real
axis. The curve does not meet `∂hull(B_n)`. Its sites are not boundary
sites of `B_n`, since those are in `I_n`, and the edge between two
interior points of a convex set lies in its interior.

*Step 3: the arm.* By `A_n(UL)` there is a K-path `G` in `UL` from `0`
to a boundary site `b` of `B_n`, and `b` lies on `∂hull(B_n) ∩ Q`. Since
`Q` is convex, the curve of `G` lies in `Q`.

*Step 4: interleaving.* In the cyclic order of `∂Q` we meet `0`, then
`s` (strictly inside the real-axis side), then `b` (on the closed outer
arc from `(-n,0)` to `t*`), then `t` (strictly inside the imaginary-axis
side). These are four distinct points in the order
`p1 = 0, q1 = s, p2 = b, q2 = t`. Lemma 2.2 makes the curves of `G` and
of `P'` up to `t` intersect, and Lemma 2.1 forbids that. ∎

*Proof of (b).* The argument is the same. Take `r` to be the last visit
to `S_n` before the first visit `m'` to the positive axis. Every site in
between lies off the real axis: real-axis sites are in `S_n`, on the
positive axis, or the boundary sites `(±n,0)`. So `P'` lies on one side,
say `y >= 0`. Use `Q = UH ∩ hull(B_n)`, whose boundary is the segment
`[-n,n]` of the real axis followed by the upper outer arc. The cyclic
order is `0`, `s ∈ (-n,0)`, `b` on the closed upper arc, and
`v_{m'} ∈ (0,n)`. Lemmas 2.1 and 2.2 give the contradiction. ∎

**Lemma 2.4 (the flipped triangulation).** Colour a site of `B_n` black
if it lies in `I_n` and white otherwise. Call a rhombus `a, u, b, v` of
the lattice (short diagonal `uv`) *checkerboard* if `a` and `b` are black
and `u` and `v` are white. Then:

(1) A step `u -> v` between two white sites is a pinch if and only if
`uv` is the short diagonal of a checkerboard rhombus. A jump between two
black sites that are not adjacent crosses a checkerboard rhombus or can
be replaced by two adjacency steps.

(2) Two checkerboard rhombi never share a triangle. So flipping the
diagonal `uv -> ab` in every checkerboard rhombus turns the lattice
triangulation of `hull(B_n)` into a triangulation `Γ_n`.

(3) Black paths in `Γ_n` are exactly the K-paths up to inserting
adjacency steps. White paths in `Γ_n` are exactly the pinch-free
non-`I_n` paths.

*Proof.* (1) A common neighbour of an interior pair `u, v` that lies
outside `B_n` would make `u` a boundary site, and boundary sites are
black. So a pinch between white sites has both common neighbours in
`I_n`, which makes the rhombus checkerboard. If a jump `a -> b` crosses a
rhombus with `u` or `v` black, then `a, u, b` or `a, v, b` is a black
adjacency path. (2) A triangle has at most one edge whose ends are both
white and whose opposite vertex is black, and a checkerboard rhombus
needs exactly such an edge in each of its two triangles. So each triangle
lies in at most one checkerboard rhombus, and the flips act on disjoint
quadrilaterals. (3) follows from (1) and (2). ∎

**Theorem 2.5 (duality on the one-arm event).**
`D'_n(0) ∩ C_n = A_n(UH) ∩ A_n(LH)`.

*Proof.* The inclusion `⊇` is Theorem 2.3(b), since `A_n(W) ⊆ C_n`. For
`⊆`, assume `C_n` and `D'_n(0)`. By the reflection of Lemma 1.2 it is
enough to prove `A_n(UH)`.

Let `T` be the union of the lattice triangles whose three vertices lie
in `B_n ∩ {j >= 0}`. This is a closed polygon, the zigzag upper half of
`B_n`. Its boundary vertices are the real-axis sites of `B_n` together
with the sites of `∂B_n` with `j >= 0`. A site with `j >= 1` that is not
in `∂B_n` has all six of its triangles in `T`. Build a
triangulation `Γ^+` of `T` by flipping every checkerboard rhombus that
lies entirely in `T`, and keeping every other edge.

Let `a, u, b, v` be a checkerboard rhombus. The `j`-values of consecutive
unit steps never have opposite signs, so `j(u)` and `j(v)` lie between
`j(a)` and `j(b)`. Hence, if `a` and `b` lie in `T`, the whole rhombus
does. If only one of its triangles lies in `T`, then `uv` lies on the real
axis. So `Γ^+` is a triangulation of the disk `T`. Its black edges are
K-steps with both ends in `T`. Its white edges are pinch-free steps in
`T`, together with some white edges `uv` on the real axis.

Split `∂T` into four arcs in cyclic order:

* `A1 = {0}`, which is black because we are on `C_n`;
* `A2`, the sites `(i,0)` with `1 <= i <= n-1`;
* `A3`, the sites of `∂B_n` with `j >= 0`, all of them black;
* `A4`, the sites `(i,0)` with `-n < i <= -1`.

By the Hex lemma, which holds for any 2-coloured triangulation of a disk
with its boundary cut into four arcs, there is either a black path of
`Γ^+` from `A1` to `A3`, or a white path of `Γ^+` from `A2` to `A4`.

In the first case, the black path is a K-path in `UH` from `0` to `∂B_n`,
by Lemma 2.4(1), so `A_n(UH)` holds.

In the second case, take a sub-path from its last site in `A4` to its
next site in `A2`. None of its edges joins two sites of the same arc, so
none of them is one of the kept axis edges. Every such edge joins two
real-axis sites on the same side of the black origin. The sub-path is
therefore a pinch-free non-`I_n` path from `S_n` to the positive axis,
which contradicts `D'_n(0)`. ∎

So on the one-arm event, the axis-to-axis box event is *exactly* the
two-half-plane K-arm event. Statement (ii), restricted to `C_n`, is
therefore a statement about `P(A_n(UH) ∩ A_n(LH))`. The data in
Section 4 confirm the identity sample by sample, and also show that the
quadrant analogue fails: `D'_n(pi/2) ∩ C_n` is strictly larger than
`A_n(UL) ∩ A_n(LL)`. A white crossing of the quadrant that ends next to
the imaginary axis need not reach `{x > 0}`.

## 3. Product bounds and the reduction of (H)

**Corollary 3.1.**
`P(D'_n(pi/2)) >= P(A_n(UL))^2` and `P(D'_n(0)) >= P(A_n(UH))^2`.

*Proof.* The Bernoulli measure on the finitely many interior sites of
`B_n` is a product measure. By Lemma 1.1 the events `A_n(UL)` and
`A_n(LL)` are increasing, so the Harris-FKG inequality gives
`P(A_n(UL) ∩ A_n(LL)) >= P(A_n(UL)) P(A_n(LL))`. Lemma 1.2 makes the two
factors equal, and Theorem 2.3(a) finishes the first bound. The second
follows in the same way from Theorem 2.3(b). ∎

**Corollary 3.2 (floor).** `A_n(W) ⊆ {0 ∈ I_n}`, so
`P(A_n(W)) <= pi(n) = n^{-5/48+o(1)}` for every wedge `W`.

**Corollary 3.3 (reduction of (H)).** Suppose that
`P(A_n(UL)) >= c n^{-alpha}` for some `alpha < 3/16` and all `n`. Then
(H) holds: `P(D_n) >= c' pi(n)^beta` for some `beta < 18/5`.

*Proof.* By Corollary 3.1 and the inclusion `D'_n(pi/2) ⊆ D_n`
(`fpbs-cle6-hull-wedge-event-is-not-the-box-event`, Theorem 1(c)),
`P(D_n) >= c^2 n^{-2 alpha}`. Pick `beta` with
`2 alpha / (5/48) < beta < 18/5`. This is possible because
`2 alpha < 3/8 = (5/48)(18/5)`. Since `pi(n) <= n^{-5/48 + eps}` for
large `n` and any `eps > 0`, we get
`pi(n)^beta <= n^{-beta(5/48 - eps)} <= n^{-2 alpha}` once `eps` is
small, and the finitely many small `n` are absorbed into `c'`. ∎

So the gate needs one increasing, one-sided event, a single K-arm in a
90-degree wedge, instead of the two-sided box event. The admissible window
is `alpha ∈ [5/48, 3/16)`.

**Conditional form.** Every `A_n(W)` contains the one-arm event
`C_n = {0 ∈ I_n}`. Harris-FKG pays for this shared arm twice, and so
cannot see the sharing. The statement that would repair this is

    (CD)   P(A_n(UL) ∩ A_n(LL)) >= n^{-o(1)} P(A_n(UL)) P(A_n(LL)) / P(C_n).

(CD) says the two wedge arms are asymptotically independent given the
one-arm event. If (CD) holds, then Theorem 2.3(a) and the proof of
Corollary 3.3 give (H) as soon as `2 alpha - 5/48 < 3/8`, that is,
`alpha < 23/96 ≈ 0.2396`. (CD) is a correlation inequality for the
measure conditioned on `C_n`. That measure is not an FKG measure in
general, because `C_n` is not closed under the meet of configurations.
So (CD) does not follow from Harris-FKG. It is OPEN. Section 4 measures
the ratio in (CD) directly.

The half-plane version (CD_H) is the same inequality with `UH` and `LH`.
By Theorem 2.3(b), it gives `zeta(0) <= 2 alpha_H - 5/48`, and hence
statement (ii), `zeta(0) < 3/16`, as soon as `alpha_H < 7/48`. By
Theorem 2.5, on `C_n` this is the only route. There, `D'_n(0)` *is* the
two-half-plane arm event.

**Corollary 3.4 (no product certificate for (ii)).** Let `E` and `F` be
any events contained in `C_n`, for instance any arm events `A_n(W)`.
Then `P(E) P(F) <= pi(n)^2 = n^{-5/24+o(1)}`. Since `5/24 > 3/16`, no
lower bound `P(D'_n(0)) >= c P(E) P(F)` can prove (ii). Neither can one
with more factors. A proof of (ii) must use the fact that the arms share
their one-arm part. That is the content of (CD_H).

*Proof.* Corollary 3.2 and the one-arm asymptotics
`pi(n) = n^{-5/48+o(1)}` (Lawler-Schramm-Werner) give the bound, and
`2 · 5/48 = 5/24 = 0.2083 > 0.1875 = 3/16`. ∎

## 4. Measurements (NUMERICAL)

The code is `experiments/fpbs-wedge-k-arm-2026-09-18/karm.c`, and all
output is in `results.txt`. It uses the same box, colouring and pinch
rule as `tri_wedge.c` of `fpbs-box-event-wedge-angle-law-refutes-restriction`.
In each sample the box sizes are nested, `n = 8, 16, ..., N`. The K-arm
search is a breadth-first search over `I_n ∩ W`, with 6 adjacency moves
and 6 jumps. Exponents are the least-squares slopes of `-log2 P` over the
last three doublings. Errors are from a 20-block jackknife.

**Inclusions and duality.** Over 9046 samples, which is about 60000
`(sample, n)` pairs, there were:

* no violation of Theorem 2.3(a) or 2.3(b);
* no pair with `D'_n(0) ∩ C_n ≠ A_n(UH) ∩ A_n(LH)`, as Theorem 2.5
  requires;
* 909 pairs in which `D'_n(pi/2) ∩ C_n` strictly contains
  `A_n(UL) ∩ A_n(LL)`.

**Exact small case.** Enumerating all `2^23` colourings of the interior
of `B_3` (`exh.c`) gives:

| quantity | exact value |
|---|---|
| `P(C_3)` | 0.482817 |
| `P(A_3(UL))` | 0.455221 |
| `P(A_3(UL) ∩ A_3(LL))` | 0.430632 |
| `kappa_Q` | 1.003329 |
| `P(A_3(UH))` | 0.480162 |
| `P(A_3(UH) ∩ A_3(LH))` | 0.477507 |
| `kappa_H` | 0.999969 |

At `n = 2` all seven events coincide, with probability 0.492188.

**Exponents.**

| event | `N = 256`, 7189 samples, fit over `n = 32..256` | `N = 512`, 1857 samples, fit over `n = 64..512` |
|---|---|---|
| `A_n(UL)` | 0.180(6) | 0.192(13) |
| `A_n(LL)` | 0.185(7) | 0.173(14) |
| `A_n(UH)` | 0.127(4) | 0.121(9) |
| `A_n(LH)` | 0.122(5) | 0.118(10) |
| `A_n(UL) ∩ A_n(LL)` | 0.262(9) | 0.272(18) |
| `A_n(UH) ∩ A_n(LH)` | 0.151(5) | 0.144(12) |
| `D'_n(pi/2)` | 0.265(7) | 0.276(16) |
| `D'_n(0)` | 0.145(4) | 0.146(9) |
| `C_n` (exact 5/48 = 0.1042) | 0.101(4) | 0.095(6) |

A third run used mode 1: 9861 samples with `N = 256`. It averages the
four quadrant arms `UL, LL, UR, LR` and the two half-plane arms. All
fits run over `n = 16..256`:

| quantity | exponent | fit over `n = 64..256` |
|---|---|---|
| `alpha_Q` | 0.190(3) | 0.188(5) |
| `alpha_H` | 0.129(3) | |
| one-arm | 0.105(3) | |
| two quadrant arms | 0.268(5) | |
| two half-plane arms | 0.155(4) | |

The two-arm exponents agree with `2 alpha - 5/48`: `0.275` for the
quadrants and `0.153` for the halves.

In this run `kappa_Q` climbs slowly, from 1.007 at `n = 8` to
1.033(8) at `n = 256`. `kappa_H` falls from 0.9993 to 0.9923(15). Both
drifts are below 0.01 in exponent per doubling. The upward drift of
`kappa_Q` works in favour of (CD), which is a lower bound.

**Decorrelation.** The ratio
`kappa_n = P(A ∩ B) P(C_n) / (P(A) P(B))` stays flat at every scale:

| `n` | 8 | 16 | 32 | 64 | 128 | 256 | 512 |
|---|---|---|---|---|---|---|---|
| `kappa(UL,LL)`, `N = 256` | 1.007 | 1.010 | 1.012 | 1.014 | 1.021 | 1.022(12) | |
| `kappa(UL,LL)`, `N = 512` | 0.997 | 1.009 | 1.004 | 1.013 | 1.007 | 0.999 | 1.009(24) |
| `kappa(UH,LH)`, `N = 256` | 0.999 | 0.999 | 0.998 | 0.997 | 0.996 | 0.993(2) | |
| `kappa(UH,LH)`, `N = 512` | 0.999 | 0.998 | 0.996 | 0.997 | 0.995 | 0.995 | 0.998(5) |

So the two-arm exponents equal `2 alpha - 5/48` to within the errors.
For the quadrants, `2(0.182) - 0.101 = 0.263`, against a measured 0.262.
For the halves, `2(0.125) - 0.101 = 0.149`, against 0.151.

This is (CD) and (CD_H) with bounded, not merely `n^{o(1)}`, loss. The
fractions `P(A_n(UL) ∩ A_n(LL)) / P(D'_n(pi/2))`, about 0.68, and
`P(A_n(UH) ∩ A_n(LH)) / P(D'_n(0))`, about 0.64, are also flat in `n`.
So the arm events carry a fixed share of the box events, and the
exponents agree: 0.265 against 0.262, and 0.145 against 0.151.

**What this says about the two statements.**

* (H) along the unconditional route of Corollary 3.3 needs
  `alpha_Q < 3/16 = 0.1875`. The data give `alpha_Q = 0.190(3)`, which
  is at or just above the threshold. This route is inconclusive, and
  probably fails by a hair.
* (H) along the (CD) route needs `alpha_Q < 23/96 = 0.240`. That holds
  with a margin of about 0.05 in `alpha`, or about 0.10 in the box
  exponent.
* (ii) along the (CD_H) route needs `alpha_H < 7/48 = 0.146`. The data
  give `alpha_H = 0.125-0.129`, and in agreement with that
  `zeta(0) = 0.145(4) < 3/16`.
* The widening inequality (i) reads `0.265 <= 2(0.145) = 0.290`. It holds
  numerically with a small margin, but this note gives no proof of it.

**Heuristic mechanism.** Given `C_n`, the arm event `A_n(W)` fails only
through a white crossing of `W` in the flipped triangulation: a hole of
`I_n` that arcs over the origin between the two bounding rays of `W`.
The data fit a picture in which the conditioned configuration near the
origin is scale invariant, like Kesten's incipient infinite cluster, and
arcs in disjoint wedges occur at nearly independent scales with a
constant rate `lambda_W` per scale.

This picture gives `alpha_W = 5/48 + lambda_W`, and it makes the two-arm
exponent additive, which is (CD). The measured rates are
`lambda_UL ≈ 0.08` and `lambda_UH ≈ 0.02`.

A proof of (CD) along these lines needs two things for the conditioned
measure: quasi-multiplicativity across scales, and arm separation for
the arc events in the two wedges.
