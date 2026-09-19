---
rg: 2
id: cone-excess-transfer-reduces-donor-lemma-to-self-bound
kind: claim
title: Excess-neutral transfer swaps empty every free cone point into its first cone neighbour, so the donor slit-pair lemma for permutation pairs reduces to self-bound cone points, which carry a loop of length at most 8 rho + 4
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this reduces its permutation case to one local lemma at self-bound cone points (with an explicit iterated F) and does not prove that lemma.
  near-exact-tuples-saturate-linear-conversion-defect: that supplies the Lipschitz bound used to iterate; this is a surgery reduction on square-tiled surfaces.
artifacts:
  - research/cone-excess-transfer-reduces-donor-lemma-to-self-bound-proof.md
  - experiments/cone-transfer-2026-09-17/transfer.py
  - experiments/cone-transfer-2026-09-17/fulltransfer.py
  - experiments/cone-transfer-2026-09-17/loopcopy.py
  - experiments/cone-transfer-2026-09-17/onecyl.py
  - experiments/cone-transfer-2026-09-17/swap.py
  - experiments/cone-transfer-2026-09-17/summary.txt
---

**ESTABLISHED (unreviewed)** (`cone-excess-transfer-reduces-donor-lemma-to-self-bound-proof`). Elementary
cut-and-paste. A strict reduction (one direction) of the permutation case of
`z2-bounded-rectangle-profile-forces-near-commuting`.

**Setting.** Read a permutation pair `(b, c)` on `d` points as a square-tiled surface `S` (`b` = right neighbour,
`c` = up neighbour). The total excess is `E = rank([b, c] - I) = sum_v (theta_v/2pi - 1) <= 2 rho`, where
`rho = Lambda_rect(b, c)`. A *swap* of two edge-disjoint grid paths with the same move word exchanges the gluings
across corresponding edges. It changes `b` and `c` by rank at most the path length each.

**Theorem A (transfer swap).** Let `A` be a vertex of angle `2 pi (k + 1)`. Let `P, Q` be paths with the same word
that leave `A` in outgoing edges one full turn (four corners) apart. Assume:
- their interior vertices are pairwise distinct and differ from `A` and from their ends;
- their ends `B != B'` both differ from `A`.

Then the swap keeps the total excess. `A` splits into a regular vertex and a vertex of angle `2 pi k`, and `B`, `B'`
merge into one vertex. So one unit of excess moves from `A` to `B ∪ B'` at cost `|P|`.

**Theorem A' (full transfer).** Take instead `k + 1` paths `P_0, ..., P_k` with one word, from the outgoing edges one
turn apart at `A`. Assume their interior vertices are pairwise distinct and differ from `A` and from all ends, and
that no end is `A` (ends may coincide). Swap `P_0` with `P_1`, then `P_1` with `P_2`, and so on up to `P_(k-1)`
with `P_k`, each time in the current surface with the same start states and word. Each swap changes the excess by
0, or by -2 exactly when the two current ends coincide. At the end every corner of `A` lies in a regular vertex.
If no swap was a -2 swap, all ends have merged into one vertex carrying the excess of `A` and of every end. The
total cost is at most `k |P_0|` in each generator.

**Theorem B (cone-ball dichotomy).** Develop the square-tiled cone of angle `2 pi (k + 1)` into `S` from the apex
`A`. Let `r*` be the least `r >= 1` such that some non-apex model vertex `v` with `|v|_inf <= r` develops to a cone
point, or two distinct non-apex model vertices with `|.|_inf <= r` develop to the same vertex. Then `r* <= 2 rho + 1`.
At radius `r*` exactly one of the following holds.
- **Self-bound.** Either a non-apex model vertex develops to `A`, or two distinct non-apex model vertices develop to
  the same *regular* vertex. In both cases `A` carries an edge loop of nonzero holonomy with `l^1` length at most
  `4 r* <= 8 rho + 4`. (Two vertices over the same plane point never collide at a regular vertex, by uniqueness of
  the backward geodesic.)
- **Free.** Neither happens, so some non-apex vertex develops to a cone point `C != A`. The `k + 1` rotated
  staircase paths from the apex to an `l^1`-minimal such vertex satisfy Theorem A', with length at most `2 r*`. The
  chain either lowers `E` by 2, when some current ends coincide, or keeps `E` and lowers the number of cone points
  by at least 1.

So in the free case the full transfer always makes progress. If `A` is the only cone point, it is self-bound.

**Corollary C (reduction).** Suppose the following *self-bound lemma* holds for some polynomial `P`. At every
self-bound cone point of a pair with profile `rho`, after padding by a flat torus, some chain of swaps of total
length `P(rho)` lowers the excess. Then every permutation pair with `Lambda_rect <= K` is within rank `F(K)` of a
commuting pair after padding, where `F` is the explicit iterate below.

Iterate the following. If some cone point is free, do a full transfer: either `E` drops by 2, or `E` stays and the
number of cone points (at most `E`) drops by at least 1. Otherwise apply the self-bound lemma: `E` drops by at
least 2. There are at most
`(E/2)(E + 1) <= rho (2 rho + 1)` steps. A step of cost `q` raises the profile by at most `2q`, by the Lipschitz
bound. A full transfer costs at most `E (4 rho + 2)`. So `F` is the sum of the step costs along the recursion
`rho_(i+1) = rho_i + 2 max(2 rho_0 (4 rho_i + 2), P(rho_i))`. This `F` depends on `K` alone but is not polynomial.
Even for linear `P`, it is `exp(O(K^2 log K))`.

**Computation** (`experiments/cone-transfer-2026-09-17`).
- `transfer.py` compared Theorem A's predicted vertex structure with direct recomputation on all admissible pairs
  of length at most 5 at the cone points of 120 random clustered perturbations of tori (seeds 1 and 5). It matched
  in 60 422 of 60 422 cases.
- `fulltransfer.py` ran the sequential chain of Theorem A' on 40 232 admissible path families (seeds 2 and 4).
  Every one of the 41 451 swaps had the predicted excess change (0 in 39 697 swaps, -2 on coinciding ends in
  1 754), and `A` ended regular in every family.
- Pairing `P_0` with `P_j` for `j >= 2` instead fails: in a first run 347 steps raised the excess by 2, because
  after the first swap `P_0` starts in the regular piece. The sequential order is necessary.
- `loopcopy.py` swapped a loop at `A` with a rotated copy ending elsewhere. The move was excess-neutral in all 767
  cases, and it only redistributes excess between `A` and the copy's end. It is a neutral move, not a lowering one.

**What it leaves.** Only the self-bound case of the donor slit-pair lemma is open: a cone point `A` whose developed
ball closes up on itself at radius `r* <= 2 rho + 1` (with no other cone point at smaller radius), giving a loop at
`A` of nonzero holonomy `u` and length at most `8 rho + 4`. The excised square of `excised-square-kills-cone-local-slit-pair-repair` and the
blocks of `lattice-donor-excises-sign-matched-cone-handles` are self-bound: each has a single cone point. There the sign-matched handle is the
lowering chain. The open step is to find, at a self-bound point, a partner loop crossing the short loop with the
sign of `det(u, w)` at length `poly(rho)`, or else a family of self-bound points where none exists.

**Both alternatives are needed (proved).** One-cylinder surfaces with `C` squares per row, height `H` and a single
`6 pi` point have `Lambda_rect <= C` for every `H`. The row index mod `H` is well defined, so every sign-matched
handle at the cone point has length at least `H`. Yet a one-edge same-vertex slit pair lowers `E` to 0
(`onecyl.py`, Proposition 7 of the proof). In the excised square it is the other way round. So the self-bound lemma
must keep both the slit-pair and the handle alternative.
