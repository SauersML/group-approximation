---
rg: 2
id: seam-surface-forces-neutral-relocation-in-self-bound-lemma
kind: claim
title: One-cylinder (1,2,3) seam surfaces have rho <= 6 but no lowering slit pair or handle shorter than their height; one neutral relocation repairs them, and tall one-cylinder surfaces are within rank 4 rho of a torus
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this refutes the no-relocation form of the self-bound step of its permutation case and settles one-cylinder surfaces, and does not prove the statement.
  cone-excess-transfer-reduces-donor-lemma-to-self-bound: that reduces the permutation case to self-bound cone points and shows handles alone fail on one-cylinder surfaces whose one-edge slit pair works; here both alternatives fail at every length below H, so the relocation clause is necessary.
  excised-square-kills-cone-local-slit-pair-repair: there cone-local slit pairs are long but a donor handle of length at most 8 works; here handles are long too.
  lattice-donor-excises-sign-matched-cone-handles: that proves the handle-excision mechanism; this family has no handle of length below H.
artifacts:
  - research/seam-surface-forces-neutral-relocation-in-self-bound-lemma-proof.md
  - experiments/self-bound-2026-09-18/swap.py
  - experiments/self-bound-2026-09-18/h2.py
  - experiments/self-bound-2026-09-18/corner.py
  - experiments/self-bound-2026-09-18/seambfs.py
  - experiments/self-bound-2026-09-18/bandcheck.py
  - experiments/self-bound-2026-09-18/chain2.c
  - experiments/self-bound-2026-09-18/run16.sh
  - experiments/self-bound-2026-09-18/chain123.py
  - experiments/self-bound-2026-09-18/rescue2.py
  - experiments/self-bound-2026-09-18/seamrepair.py
  - experiments/self-bound-2026-09-18/scanchain.py
  - experiments/self-bound-2026-09-18/summary.txt
---

**ESTABLISHED (unreviewed)** (`seam-surface-forces-neutral-relocation-in-self-bound-lemma-proof`). Elementary
cut-and-paste plus one exhaustive finite check. It answers the self-bound step of
`z2-bounded-rectangle-profile-forces-near-commuting` as posed after
`cone-excess-transfer-reduces-donor-lemma-to-self-bound`: without relocation moves the dichotomy is false; with
one neutral relocation it holds on this family.

**Setting.** A permutation pair `(b, c)` is a square-tiled surface (`b` = right neighbour, `c` = up neighbour).
The excess is `E = rank([b, c] - I)`, and `rho = Lambda_rect(b, c)`. The surface `S(H, tw)` is one horizontal
cylinder of circumference 6 and height `H`, whose top is glued to its bottom by the interval exchange that
reverses three intervals of lengths `(1, 2, 3)`, followed by the twist `tw` (`onecyl(1, 2, 3, H, tw)` in `h2.py`).
It has one cone point `A`, of angle `6 pi`, so `E = 2`.

**Theorem 1 (no short alternative).** For every `H >= 1` and every twist:
- (a) `rho <= 6`, and `A` is self-bound (it is the only cone point);
- (b) every loop at `A` with nonzero vertical holonomy has length at least `H`, so every sign-matched handle
  (two loops with `det(u, w) != 0`) has a loop of length at least `H`;
- (c) no same-vertex slit pair of length `L < H` lowers `E`. Precisely: take two paths with the same move word from
  two distinct outgoing edges of `A` of the same direction, with the `2L` edges distinct, the interior vertices
  pairwise distinct and different from `A`, and a common end. Then the end is `A` (a common regular end is
  impossible), and the swap keeps `E = 2`.

So for every polynomial `P`, once `H > P(6)` the point `A` has neither alternative (i) nor (ii) of the self-bound
step at length `P(rho)`. The same holds for seam lengths `(1, 3, 2)`.

**Theorem 2 (one relocation suffices).** For every `H` and twist, two transpositions of `c`-values on the top row
reach a torus (`E = 0`). The first keeps `E = 2`; it is a relocation swap of two one-edge paths, one from a sector
of `A`. The second is a one-edge same-vertex slit pair. The cost is `(0, 2)`.

**Proposition 3 (one-cylinder surfaces are harmless).** Let `S` be a one-cylinder surface of circumference `n` and
height `H >= n`, with top-to-bottom seam permutation `sigma`. Let `d(sigma) = min_j rank(rho_j^(-1) sigma - I)`,
where `rho_j` is the rotation by `j`. Then `d(sigma) < 4 rho`, and regluing the top row by the best rotation gives
a torus. So `S` is within rank `4 rho` of a commuting pair, with `b` unchanged. This covers the family above and
the one-cylinder family of `cone-excess-transfer-reduces-donor-lemma-to-self-bound` (Proposition 7 there).

**Proof ideas.**
- (a) and (b) are Proposition 7 of the w14 proof with `C = 6`: the row index mod `H` is a height function.
- (c) The key tool is a corner rule. After a loop-pair swap at `A`, the corners of `A` form the cycles of
  `(a_P a_Q) o nu o (g_P g_Q)`, where `nu` is the ccw corner rotation and `a`, `g` are the first and last corners.
  All other vertices keep their angles.
  - A loop of length `< H` has height range below `H/2`, so it lives near the seam.
  - The two paths have equal heights at all times. So they visit the seam's three regular vertices together, and at
    most once.
  - In each half-cylinder, the `Q`-excursion is the `P`-excursion translated by `D` columns. Disjointness of the
    translates forces horizontal displacement `|Delta| < dist(D, 6Z) <= 3`.
  - So every excursion can be replaced by a depth-1 U-shape with the same first and last edges. The corner data
    are unchanged, so every admissible pair is corner-equivalent to one inside the three-level band at the seam.
  - `bandcheck.py` enumerates that band exhaustively for all six twists: 40 admissible pairs, none lowering.
- Theorem 2: the seam permutation is a rotation times a 3-cycle, and a 3-cycle is a product of two
  transpositions.
- Proposition 3: `c^H` acts as `sigma` on every row, so `rho >= H rank([R^s, sigma] - I)/(s + H)`. Averaging the
  moved points of `[R^s, sigma]` over `s` gives at least `d(sigma)`.

**Computation** (`experiments/self-bound-2026-09-18`, all exhaustive).
- Corner rule: 1720 of 1720 admissible loop pairs matched, on five surfaces.
- Band: 40 pairs, 0 lowering, for `(1, 2, 3)` and `(1, 3, 2)` at every twist. Controls: `(2, 2, 2)` has 84 lowering
  pairs of 156, and `(1, 2, 4)` has 4 of 28.
- Beyond vertex-admissibility, `chain2` finds no edge-distinct single same-word swap from two sectors of `A` that
  lowers `E` at length `<= 15`, on `S(20, tw)` for all six twists.
- Theorem 2's chains were checked for `H = 3, 5, 7`, and `chain123.py` finds at least 8 chains for every `2 <= H <= 9`.
- Proposition 3 was checked on all `sigma` in `Sym(n)` for `n <= 7`, with `H = n`.
- On all 10859 `H(2)` surfaces with at most 16 squares, a chain of at most two swaps (a neutral one, then a slit
  pair, with a 1x1 donor) of total length at most 4 lowers `E`.

**What it leaves.** The self-bound lemma of Corollary C must allow neutral relocation moves before the slit pair
or handle. Single swaps are not enough, even at bounded profile and with a single cone point. The natural next
step is the cylinder form of Proposition 3. Every rational direction of a square-tiled surface is completely
periodic, so a self-bound point's short loop `u` gives a cylinder decomposition in direction `u`. Show that each
cylinder is either tall, and then seam-repairable by rotation matching at cost `O(rho)`, or short, and then
crossed by a loop of length `poly(rho)` that supplies alternative (ii).
