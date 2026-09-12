---
rg: 2
id: kl-three-coincidence-residue-words-inject-with-room-for-loops
kind: claim
title: Length-six residue words with three same-sign coincidences inject when the loop orders leave room for a weight and the light label avoids short loop words
distinct_from:
  kl-length-six-one-coincidence-words-inject: that allows exactly one coincidence under infinite-order conditions on the light cycle; this treats the three-coincidence shapes, whose heavy triple costs three units of weight and leaves one unit for the two loops.
  kl-sign-index-two-infinite-order-loops-inject: that needs both loops of infinite order; this allows one torsion loop, or two loops of order at least four, at the price of conditions on the lone light label.
  kl-length-six-coincidence-saturated-torsion-residue: that is the open statement for all residue shapes and loop orders; this settles the three-coincidence shapes whenever 2/k_y + 2/k_x <= 1 and the light label avoids short words in the loops.
  kl-length-six-residue-squares-and-fourth-powers-inject: that settles four sub-cases, g equal to a loop coefficient, by substitution and for every loop order; this settles the same shapes by weights when the loop orders allow it.
---

Let `G` be any group and `w` a word of one of the normalized residue shapes of
`kl-length-six-coincidence-saturated-torsion-residue` that close three
same-sign coincidences:
- `+++++-`: `(1,1,1,g)`, `(1,1,g,1)`, `(1,g,1,1)`, `(g,1,1,1)`;
- `++++--`: `(1,1,g)`, `(g,1,1)`, `(g,g,g)`.

Here `g != 1`, and `y` and `x` are the loop coefficients at `t^-` and `t^+`, of
orders `k_y, k_x in {2, 3, ..., infinity}`.

Three same-sign corners form a heavy triple, pairwise closing trivial 2-cycles,
and the fourth corner is light:
- in the six *P-light* shapes the light corner is the P-label `g` and every heavy
  label is `1`;
- in `(g,g,g)` the heavy labels are `g` and the light corner is the N-label `1`.

**Theorem.** Suppose some `alpha in [0, 1]` satisfies `alpha k_y >= 2` and
`(1 - alpha) k_x >= 2`, where a loop of infinite order passes its test whatever
its weight, and:
- (C1) `g != y^j x^i` for all integers `i, j` with `alpha |j| + (1 - alpha) |i| < 1`;
- (C2) for all nonzero integers `i, j` with `alpha |j| + (1 - alpha) |i| < 2`:
  - `g x^i g^(-1) != y^j` in the six P-light shapes;
  - `x^i != y^j` in the shape `(g,g,g)`.

Then `G -> (G * <t>)/<<w>>` is injective, and every reduced spherical picture
over `<G, t | w>` is empty.

## Corollaries

1. **One loop of infinite order.** Let `x` have infinite order and `y` finite
   order, and take `alpha = 1`.
   - (C2) holds automatically: conjugates of nonzero powers of `x` have infinite
     order, and `y^j` does not.
   - (C1) says `g` is not in `<x>`.

   So these shapes inject whenever `g` is not in `<x>`. Symmetrically, when `y`
   has infinite order and `x` finite order, they inject whenever `g` is not in
   `<y>`.
2. **Both loops of order at least four.** Take `alpha = 1/2`. The shapes inject
   when:
   - `g` is none of `x^(+-1)`, `y^(+-1)`;
   - the relation of (C2) fails for all `i, j` with `1 <= |i|, |j|` and `|i| + |j| <= 3`.
3. **Not covered.** No `alpha` exists when both orders are finite and
   `2/k_y + 2/k_x > 1`:
   - one loop of order two and the other of finite order;
   - orders `3` and `3`, `4` or `5`.

   Involution loops, the Leavitt case, stay open.

**The two-pair shapes leave no room.** In `(1,1,g,g)`, `(1,g,1,g)`, `(1,g,g,1)`,
`(1,g,g)`, `(g,g,1)` and `(g,1,g)`, two disjoint heavy pairs already need weight
four, the whole budget `n - 2`. A torsion loop then gets weight zero and its
power cycle defeats (WT2). So this method gives nothing there.

DERIVATION
kl-three-coincidence-residue-weight-proof
