---
rg: 2
id: lattice-donor-excises-sign-matched-cone-handles
kind: claim
title: Two crossing edge loops at a cone point with holonomies u, w and the matching crossing sign are excised by two swaps with the lattice donor Z^2/<u,w>, the first excess-neutral and the second lowering the excess by 2
distinct_from:
  two-torus-cross-slit-forces-sqrt-d-loss-in-thin-closing: that shows one-sided equivariant closing loses sqrt(d) on the cross slit; this is a two-sided, non-equivariant surgery on the square-tiled surface itself, and uses a padded donor.
  centralizer-rounding-cannot-bound-rank-distance-by-profile: that bounds one-sided centralizer rounding from below; this changes both generators and is an upper-bound tool.
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this proves one donor mechanism of the proposed donor slit-pair lemma and leaves the lemma (and the statement) open.
artifacts:
  - research/lattice-donor-excises-sign-matched-cone-handles-proof.md
  - experiments/donor-slit-pair-2026-09-17/handle.py
  - experiments/donor-slit-pair-2026-09-17/handle_check.py
  - experiments/donor-slit-pair-2026-09-17/blocks.py
  - experiments/donor-slit-pair-2026-09-17/chain2.c
  - experiments/donor-slit-pair-2026-09-17/greedy2.py
  - experiments/donor-slit-pair-2026-09-17/summary.txt
---

**ESTABLISHED (unreviewed)** (`lattice-donor-excises-sign-matched-cone-handles-proof`). Elementary cut-and-paste.
This is the donor mechanism asked for by the donor slit-pair step of `z2-bounded-rectangle-profile-forces-near-commuting`.

**Setting.** Read a permutation pair `(b, c)` as a square-tiled surface `S` (`b` = right neighbour, `c` = up
neighbour). The excess is `rank([b, c] - I)`, the total cone excess. An *edge loop* at a vertex `A` is a closed path
along grid edges from `A` to `A` that visits no vertex twice (apart from `A` at its two ends). Its *word* is its
sequence of moves (straight, left, right) and its *holonomy* is its developed displacement in `Z^2`. A *swap* of two
edge-disjoint paths with the same word exchanges the gluings across corresponding edges. At `A`, `alpha` splits the
cyclic order of corners into a *left fan* (counterclockwise from the first edge of `alpha` to its reversed last edge) and a
*right fan*.

**Theorem (handle excision).** Let `alpha, beta` be edge loops at `A` with holonomies `u, w`. Suppose:
- `alpha` and `beta` have no common edge and no common vertex other than `A`;
- `det(u, w) != 0`;
- **(H1)** `beta` crosses `alpha` at `A`: it leaves into one fan of `alpha` and returns from the other. It leaves
  into the right fan exactly when `det(u, w) > 0`;
- **(H2)** in the lattice torus `T = Z^2/<u, w>` (area `|det(u, w)| <= |alpha| |beta|`), the paths `alpha', beta'` with
  the same words and first sides, starting at the lattice point `0`, are simple and meet only at `0`.

Pad `(b, c)` with the commuting pair of `T`. Then:
1. Swapping `alpha` with `alpha'` leaves the excess unchanged. It inserts a flat cylinder along `alpha` and splits `A`
   into two vertices `A_L`, `A_R`.
2. Afterwards `beta` and `beta'` both run from `A_R` to `A_L` (or both from `A_L` to `A_R`). So swapping them lowers
   the excess by exactly 2.
3. The chain changes `b` by rank at most `V_alpha + V_beta` and `c` by rank at most `H_alpha + H_beta` (vertical and
   horizontal edge counts). So `rho` grows by at most `2(|alpha| + |beta|)`.

Only the simplicity of `alpha` and `alpha'` is needed for item 1.

**Where it applies.**
- It is exactly the repair of w12-124's excised-square example (still pending in its land queue), where every
  cone-local slit-pair repair costs at least `n/4 - 1/2`. Here `|alpha| = |beta| = 1` with a `1 x 1` donor.
- Excising a `k x l` block of the `n x n` torus into its own torus gives one `6 pi` point. It is repaired at total
  length `k + l` with a `k x l` donor. The measured profile lower bounds are `3.33, 4.71, 6.0, 6.67, 7.22` for
  `(k, l) = (2,2), (3,3), (4,4), (2,5), (5,5)`, so the cost is linear in `rho` on this family (`blocks.py`).

**Computation.**
- **The sign condition** (`handle_check.py`). Every pair of simple loops satisfying (H2) with `det != 0` was
  enumerated, up to length 5, on these surfaces: excised squares, three excised blocks, and the excess components
  of 40 random clustered perturbations. Among the 8298 pairs:
  - the first swap was excess-neutral in all of them;
  - the second swap lowered the excess, by exactly 2, in precisely the 600 pairs satisfying (H1);
  - it lowered nothing in the 3014 crossing pairs with the opposite sign, or in the 4684 pairs that do not cross.
- **The donor two-swap step itself** (`chain2.c`). The search allows a first swap that is excess-monotone and may use
  a padded donor of size `1x1`, `2x1`, `1x2` or `2x2`, followed by a lowering same-vertex swap (`L1 <= 3`, `L2 <= 5`).
  - It resolves all 13 greedy stalls of w12-124, including the 8 not investigated there. The total length is at most
    8, and at most 5 with the best donor.
  - Iterated greedily on 737 random clustered perturbations (w12-124's distribution, seeds 5, 6 and 7), it never
    stalls. The largest single chain has 8 edges.
- **Stalls are not arithmetic.** In the 8 uninvestigated stalls (trials 78, 130, 131, 133, 152, 153, 169, 198), the
  stuck excess-2 component has the full area of the original torus. What stalls them is that w12-124's greedy accepts
  only lowering first swaps. None of the 13 stalls has a sign-matched handle with loops of length at most 5
  (`handle.py`). In the decoded chains (trials 29, 78 and 130), the first move is a neutral transposition that moves
  or merges cone points, and a same-vertex slit of 1 or 2 edges then lowers the excess. Every stall has a donor-free
  chain. A donor shortens the chain only in trials 46, 64 and 138, from 7, 8 and 7 edges to 4, 4 and 5.

**What it leaves.** The donor slit-pair lemma needs, at every pair with excess and profile `rho`, one of the following
at length `poly(rho)`:
- a same-vertex slit pair;
- a sign-matched handle;
- a neutral cone move that produces one of the first two.

The lemma is still open. The cone-radius bound of w6-124 supplies a short saddle connection or loop at every cone
point, but not the partner loop with the right sign.
