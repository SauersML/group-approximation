---
rg: 2
id: kl-relative-weight-test-gives-injectivity-curvature-proof
kind: route
title: Put angle pi(1 - theta) at every picture corner and count curvature on the capped disc
target: kl-relative-weight-test-gives-injectivity
requires: []
---

This is the curvature section of `kl-four-same-sign-corner-words-weight-proof`,
stated for an arbitrary weight. That section uses only (WT1), (WT2),
`theta >= 0` and the hypotheses on `w` listed in the target, never the
particular weights chosen there. Notation is as in the target. Write
`P = <G, t | w>` and `G(P) = (G * <t>)/<<w>>`.

**Orientability.** No cyclic permutation of `w` equals a cyclic permutation of
`w^(-1)`, because `deg_t(w^(-1)) = -deg_t(w) != deg_t(w)`.

**Van Kampen.** By the relative van Kampen lemma (Howie; Bogley--Pride), if
`1 != g in G` dies in `G(P)`, then some picture over `P` on a disc `D` has
boundary label `g` and no arc meeting `∂D`. Take one with the fewest discs and
delete floating circles.
- It has at least one disc, since a picture with no disc has boundary label `1`.
- It has no dipole, since cancelling a dipole removes two discs.

**Regions read cyclically reduced admissible paths.** Going once around a
boundary component of a region, the successive corners of discs read a closed
path in the star graph, one edge per corner.
- Suppose two consecutive corners, on discs joined by one arc, read an edge
  and then the same edge reversed. Then the two discs carry the same cyclic
  permutation of `w` with opposite orientations, reflected across the arc.
  The edge fixes the whole cyclic permutation because `w` is not a proper
  power, and the orientations are forced opposite by orientability. That is a
  dipole. So every region path is cyclically reduced.
- A simply connected region not meeting `∂D` has label `1` in `G`, by the
  definition of a picture over a relative presentation. Its path is
  admissible, so by (WT2) its corner weights sum to at least `2`.

**Count.** Cap `∂D` with a disc to get a picture on `S^2`. Discs (`V`), arcs
(`E`) and regions satisfy

```text
V - E + sum_f chi(f) = 2,    chi(f) = 2 - b_f,
```

where `b_f` is the number of boundary components of the region `f`. This holds
for any graph on `S^2`, connected or not: with `c` components and `F` regions,
`V - E + F = 1 + c` and `sum_f (b_f - 1) = c - 1`.

At a corner whose star-graph edge is `i`, put the angle `alpha = pi(1 - theta_i)`,
and set

```text
kappa(v) = 2 pi - sum_(corners at v) alpha,
kappa(f) = 2 pi chi(f) - sum_(corners in f) (pi - alpha).
```

Every disc has `n` arc ends and `n` corners, so there are `2E` corners in all,
and `sum_v kappa(v) + sum_f kappa(f) = 2 pi (V - E + sum_f chi(f)) = 4 pi`.
On the other hand:
- each disc carries the `n` corners of `w`, so
  `kappa(v) = 2 pi - pi sum_i (1 - theta_i) <= 0` by (WT1);
- a simply connected region not containing the cap has
  `kappa(f) = 2 pi - pi (sum of theta over its corners) <= 0` by (WT2);
- a region with `b_f >= 2` has `kappa(f) <= 0`, because `theta >= 0`;
- the region containing the cap has `b_f >= 1` after capping, so
  `kappa(f) <= 2 pi`, because `theta >= 0`.

So the total is at most `2 pi < 4 pi`, a contradiction. Hence
`G -> G(P)` is injective.

A reduced spherical picture with at least one disc has no cap region, and the
same count gives a total of at most `0 < 4 pi`. So every reduced spherical
picture over `P` is empty.

**Not verified at source.**
- The conditions (WT1) and (WT2) are the Bogley--Pride weight test
  (*Aspherical relative presentations*, Proc. Edinburgh Math. Soc. 35 (1992)),
  as restated in Ahmad--Al-Mulla--Edjvet, arXiv:1604.00163v2. Bogley--Pride
  was not reached, and this route does not use their theorem.
- The relative van Kampen lemma and the dipole step are standard picture
  calculus. They were not re-read in Howie or in Bogley--Pride, which is the
  same trust surface as `kl-four-same-sign-corner-words-weight-proof`.
