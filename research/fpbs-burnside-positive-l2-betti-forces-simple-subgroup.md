---
rg: 2
id: fpbs-burnside-positive-l2-betti-forces-simple-subgroup
kind: claim
title: In a large odd Burnside group a subgroup with positive first L2 Betti number has an infinite simple subgroup of bounded finite index, so the L2 route to positive upper cost only sees simple subgroups
distinct_from:
  fpbs-burnside-positive-upper-cost: that open root asks for c_n > 1; this shows that the L2-Betti lower bound can supply c_n > 1 only through an infinite simple subgroup with positive beta_1, and that beta_1(B(m,n)) = 0 for m >= 3.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that open claim asserts cost one for every action; its L2 shadow is exactly Gaboriau Theorem 6.8, which is imported and used here, so no L2 invariant can obstruct it.
  fpbs-burnside-common-upper-cost: that gives C^*(H) = c_n for infinite H; this uses it only as a uniform upper bound on beta_1 of finite-index subgroups.
---

**PROPOSED ESTABLISHED (written proof over established nodes and a citation import; see the proof route).**

**Setting.** `n` is odd and in the common scope of `fpbs-burnside-common-upper-cost`,
`fpbs-burnside-embedding-input` and `fpbs-burnside-normal-closure-split` (so in particular `n >= 665`), `m >= 2`,
`G = B(m,n)`, and `c_n = C^*(G)`, so `1 <= c_n <= 2 - 2/n`. `beta_1` is Gaboriau's first L2-Betti number of a
countable group.

**Theorem.**
1. **Vanishing for the groups themselves.** `beta_1(B(m,n)) = 0` for every `m >= 3`.
2. **Simple-subgroup reduction.** Let `H <= G` be infinite with `beta_1(H) > 0`. Then:
   - every finite-index subgroup of `H` has index at most `(c_n - 1)/beta_1(H) < 1/beta_1(H)`;
   - `H` has a smallest finite-index subgroup `H_0`, which is normal in `H`;
   - `H_0` is an infinite simple group;
   - `0 < beta_1(H_0) = [H : H_0] beta_1(H) <= c_n - 1 <= 1 - 2/n`.
3. **Converse.** If some infinite `S <= G` has `beta_1(S) > 0`, then `c_n >= 1 + beta_1(S) > 1`. For `m >= 3`,
   `B(m,n)` then has free actions of different cost: some have cost near `1`, and some have cost near `c_n`.

**Consequence for the programme.**
- The L2 lower-bound route for `fpbs-burnside-positive-upper-cost` is equivalent to finding an infinite simple
  subgroup `S` of a large odd Burnside group with `beta_1(S) > 0`.
- Every infinite subgroup that is not virtually simple has `beta_1 = 0`, and so is invisible to this route. In
  particular `B(m,n)` (`m >= 3`), all its finite-index subgroups, and every infinite subgroup with an infinite normal
  subgroup of infinite index are invisible.
- The recorded death of the route ("even a positive value would raise both costs together") is incomplete. Under
  `fpbs-burnside-common-upper-cost`, a positive `beta_1` of any infinite subgroup already gives `c_n > 1`, since
  `C^*` is common to all infinite subgroups.

**Scope.**
- `m = 2`: not asserted. The reduction in item 2 applies to `B(2,n)`, but no nontrivial normal subgroup of
  infinite index in its minimal finite-index subgroup is constructed here.
- No infinite simple subgroup of `B(m,n)` is constructed or excluded here, so `c_n > 1` stays open.

**Novelty caveat.** Item 1 and the normal-subgroup step are direct applications of Gaboriau's Theorem 6.8. The
contribution is the combination with the common upper cost, which bounds the index and produces the simple
subgroup. This combination was not found in the graph or in the sources read; priority is not asserted.
