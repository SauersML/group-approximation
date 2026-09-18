---
rg: 2
id: half-tube-lattice-points-are-edge-split-vertices
kind: claim
title: In rank at least three, every primitive lattice point within sup-distance 1/2 of the ray of a generic point, in a cell's own coordinates, is a vertex of an edge-split descendant of the cell containing that point
distinct_from:
  edge-splits-cut-every-rational-hyperplane: that is cofinality, a statement about cutting a cell by a hyperplane; this is vertex reachability, a statement about which lattice points become vertices of descendants around a fixed point.
  rank-two-synchronization-off-totally-irrational-rays: that reduces rank-two synchronization at totally irrational rays to a shared-vertex condition; this supplies shared vertices, in every rank, at every point lying on no rational hyperplane.
  unimodular-cells-synchronize-under-edge-splits: that is the synchronization statement; this is the vertex lemma that its proof route uses at generic points.
artifacts:
  - research/artifacts/gq-bh-free-61-half-tube-checks.md
---

**ESTABLISHED** (lane bh-free-61, 2026-09-18). Lane proof, elementary, not
independently reviewed. No priority claimed.

## Setting

Notation of `edge-splits-cut-every-rational-hyperplane`, in `R^n` with `n = m + 1`.
- A cell `K = cone(b_1, …, b_n)` has a frame `B ∈ GL_n(Z)` with columns `b_k`.
  Coordinates in `K` are `B^{-1}x`.
- Splitting `K` along `(i, j)` gives two children. In `K`'s coordinates `y`, the child
  `{y_i ≥ y_j}` has coordinates `y − y_j e_i`.
- A point `ζ` is *generic* if it lies on no rational hyperplane. Then its coordinates in
  every cell are positive (when `ζ ∈ K`) and pairwise distinct, because
  `y_i = y_j` is a rational hyperplane.

**The joint game.** Fix a primitive `w ∈ Z^n` and a generic `ζ`, both in `K`, with
coordinates `u` and `z`.
- A *move* `(i, j)` is allowed when `u_i ≥ u_j` and `z_i > z_j`. It replaces `u_i` by
  `u_i − u_j` and `z_i` by `z_i − z_j`, and `K` by the child `{y_i ≥ y_j}`, which contains
  both points.
- The game is *won* when `u` is a unit vector `e_k`. Then `w = b_k` is a vertex of a
  descendant of `K` containing `ζ`.
- Conversely, every descendant of `K` containing `ζ` and having `w` as a vertex arises
  this way: the chain of cells from `K` to it contains `w` and `ζ` throughout.

So `w` is a vertex of a descendant of `K` containing `ζ` if and only if the joint game
from `(u, z)` can be won.

## Statement

**Half-tube lemma.** Let `n ≥ 3`, `K` a cell, `ζ ∈ K` generic and `w ∈ K` primitive, with
coordinates `u, z`. Suppose `|u − t z|_∞ < 1/2` for some real `t > 0`. Then the joint game
from `(u, z)` can be won. So `w` is a vertex of a cell of `Desc(K)` containing `ζ`.

**Corollary (shared vertices).** Let `K_1, K_2` be cells containing a generic point `ζ`.
Some primitive `w` is a vertex both of a cell of `Desc(K_1)` containing `ζ` and of a cell
of `Desc(K_2)` containing `ζ`.

## Proof of the lemma

Put `d = u − t z`, so `|d|_∞ < 1/2`. Keep `t` fixed throughout.

**Key inequality.** Let `i ≠ j` with `d_i d_j ≥ 0` and `z_i > z_j`. Then the move `(i, j)`
is allowed, and after it `|d|_∞ < 1/2` still holds.
- `u_i − u_j = t(z_i − z_j) + (d_i − d_j)`. The first term is positive. Since `d_i, d_j`
  have the same sign and absolute values below `1/2`, `|d_i − d_j| < 1/2`. So
  `u_i − u_j > −1/2`, and `u_i ≥ u_j` because both are integers.
- The move changes `d` only in slot `i`, to `(u_i − u_j) − t(z_i − z_j) = d_i − d_j`,
  which has absolute value below `1/2`.

**A same-sign pair always exists.** Among `n ≥ 3` real numbers, two satisfy
`d_i d_j ≥ 0`. Order them by `z`, which is possible since `z_i ≠ z_j`. So the invariant
`|d|_∞ < 1/2` can be kept forever. What remains is to reach a unit vector.

**A strategy that terminates.** Let `P = {k : u_k > 0}`. As long as `u` is not a unit
vector, `|P| ≥ 2`, because `w` is primitive.
- *Case A.* Two indices of `P` have `d_i d_j ≥ 0`. Make that move. It lowers `|u|_1` by
  `u_j ≥ 1`.
- *Case B.* Otherwise the values `d_k` for `k ∈ P` are pairwise of strictly opposite sign,
  so `P = {a, b}` with `d_a > 0 > d_b`. Then `Z_0 = {k : u_k = 0}` is nonempty, since
  `n ≥ 3`, and `d_k = −t z_k < 0` for `k ∈ Z_0`.
  - For `k ∈ Z_0`, the pair `(b, k)` has the same sign. If `z_k > z_b`, the key inequality
    would give `u_k ≥ u_b ≥ 1`, which is false. So `z_b > z_k`, and the move `(b, k)` is
    allowed. It leaves `u` unchanged and raises `d_b` by `t z_k`.
  - Case B moves never touch coordinates in `Z_0`. So `d_b` rises by at least
    `t · min_{Z_0} z > 0` per move and stays below `1/2`. After finitely many moves
    `d_b ≥ 0`, and Case A applies.
- `|u|_1` is a positive integer that drops at every Case A move, and between Case A
  moves there are finitely many Case B moves. So the strategy stops, and it can only stop
  at a unit vector.

## Proof of the corollary

- Scale `ζ` by a positive factor so that `ζ = (ε, α_2, …, α_n)` with `ε = ±1`. This is
  possible because a generic point has no zero coordinate. Let `B_1, B_2` be the frames of `K_1, K_2`, and put
  `ρ = min_s 1/(2‖B_s^{-1}‖_∞)`, the operator norm for `|·|_∞`.
- Dirichlet's simultaneous approximation gives infinitely many integers `q` with
  `|qα_i − p_i| < ρ` for all `i`. They are unbounded, since `ζ` is not a rational ray.
  Put `x = (εq, p_2, …, p_n)`, so `|x − qζ|_∞ < ρ`, and let `w = x/g` be its primitive part.
  Then `|w − (q/g)ζ|_∞ < ρ` too.
- In the frame of `K_s`, `|B_s^{-1}w − (q/g) B_s^{-1}ζ|_∞ < 1/2`, and `B_s^{-1}w > 0` once
  `q` is large, because `B_s^{-1}ζ > 0`. So `w ∈ K_s`, and the lemma applies in both
  frames.

## Remarks

- **Rank two is different.** For `n = 2` the two coordinates of `d` can have opposite
  signs and no move keeps the tube. There the correct statement is Legendre-type: the
  lattice points that become Stern–Brocot vertices around an irrational form a sparse set
  of convergents and intermediate fractions.
- **The tube is not sharp, but its scale is right.** In rank three, from `Δ`, exact game
  searches around sampled generic `ζ` found the closest losing points shrinking roughly
  like `1/|w|`: angle about `0.1` for entry sum at most 30, `0.03`–`0.04` for entry sum
  at most 90, and `0.011`–`0.018` for entry sums 200–400. The half-tube condition is
  angle of order `1/(2|w|)`. So the winning region has the half-tube's shape, larger by a
  constant factor. Details are in the artifact.
- **Checks** (MSI, single core, seconds each; generic `ζ` modelled by random 56- to
  60-bit integer vectors). The strategy above was run on 860000 half-tube points in rank
  3 and on about 85000 in ranks 4, 5, 6 and 8. No step violated the key inequality or
  the invariant, and every completed run was won. An independent exhaustive game search
  agreed on all 35353 rank-3 points small enough to search. The only failures were step
  caps in ranks at least 4 at `|u|` near `10^9`, where the number of moves is bounded by
  `|u|_1` but large.

## Lesson for general BH

A continued-fraction algorithm with free choice at every step behaves quite unlike a
deterministic one.
- For a deterministic algorithm, which lattice points become vertices around a point is
  a sparse, algorithm-specific set: convergents in rank one. Comparing two such
  expansions is a Serret problem, hard in higher rank.
- With free choice, in rank at least three, a whole tube of lattice points around the
  ray becomes reachable, by a one-line pigeonhole argument on the rounding error. Two
  expansions from different cells then share a vertex by Dirichlet, and Serret-type
  synchronization reduces to a local lemma at that shared vertex.
- This is the general pattern to look for in hosts built from a lattice acting on a
  Cantorization: prove a *reachability tube* for the free-choice subdivision, then
  synchronize through a shared vertex instead of through a shared tail.
