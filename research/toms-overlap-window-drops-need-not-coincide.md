---
rg: 2
id: toms-overlap-window-drops-need-not-coincide
kind: claim
title: On a box of N ideal two-wall overlap windows every target drops somewhere, but the drops need not coincide - one node can absorb its neighbour's overlap, so a target of depth ceil(N/2) exists and the linear-depth constant is at most 1/2
artifacts:
  - experiments/toms-overlap-window-n2-2026-09-17/token_depth.py
  - experiments/toms-overlap-window-n2-2026-09-17/token_sat.py
  - experiments/toms-overlap-window-n2-2026-09-17/results.json
distinct_from:
  toms-overlap-window-cubes-force-linear-depth: that conjectures depth cN for some c; this decides N = 2 (forced depth exactly 1), shows c <= 1/2 for every N, and proves c = 1/2 for targets that split over the nodes.
  toms-transit-windows-fill-unless-their-ranks-overlap: that proves the one-node drop (Part 3); this is the many-node question, answered by a joint divisibility over all vertex slices and by an explicit target whose drops sit on one node only.
  toms-chern-swap-count-allows-depth-one-drops: that staggers drops within one swap family; this staggers them across nodes, by letting one node carry the constant bundle of its leaf maxima.
---

**ESTABLISHED** (internal derivation, unreviewed; proof `toms-overlap-window-drops-need-not-coincide-proof`).

**Setting.** As in `toms-overlap-window-cubes-force-linear-depth`, with `D = d_n c` an integer.
There are `N` nodes `nu`, with windows `I_nu`, vertex slices `Y_nu = CP^(j_nu)` and an ancestor
factor `Z`. Let `g'` be the rank of the pushforward outside the `N` node blocks. The upper
band is `U = g' + N D`, so each node has budget `D`. A window is *ideal two-wall* if it is
`A | w_1 | B | w_2 | C`, where the node data `(R(s), R(1-s))` are

- `(k-1, D-k)` on chamber `A`, `(k, D-1-k)` on `B` and `(k+1, D-2-k)` on `C`;
- `(k-1, D-k-1)` at the wall `w_1` and `(k, D-k-2)` at `w_2` (the lower semicontinuous values).

So `Pbar = k+1` and `Qbar = D-k`, which gives `kappa = 1`. The room is `3` and there are two walls,
which is the smallest forcing window of Part 4. The value of `k` may depend on `nu`. A
*target* is `Q in M_infinity(C(S x Y x Z))_+` with `psi_(n,M)(a_n) <~ Q` and `rank Q <= U`.
Its *depth* is `U - min rank Q`.

**Theorem.** Let every window be ideal two-wall.

1. *Some drop is forced.* If `N D <= min_nu j_nu`, every target has depth `>= 1`.
2. *The drops need not coincide.* For every `N` there is a target of depth exactly
   `ceil(N/2)`. For `N = 2` it is
   `Q = G ⊕ psi_1 ⊕ (Pbar_2 L_(2,+) ⊕ Qbar_2 L_(2,-))`: node 1 keeps its own pushforward
   block, and node 2 is replaced by the constant bundle of its leaf maxima. Here `G` is the
   pushforward outside the nodes. The rank is `U` on the chambers of node 1 and `U - 1` on
   its two walls, and node 2 never drops.
3. *Split targets have depth at least `ceil(N/2)`.* Suppose `Q = G ⊕ ⊕_nu Q_nu`, where `G`
   has constant rank `g'` and dominates the pushforward outside the nodes, and each `Q_nu`
   depends only on `(s_nu, y_nu, z)` and dominates the block of node `nu`. If `D <= j_nu`,
   then `Q` has depth `>= ceil(N/2)`.

**Consequences.**
- `N = 2` is decided (with `2D <= j_v`): the forced depth is exactly `1`. The two nodes'
  drops need not share a point: node 2 need not drop at all, because it absorbs its
  overlap into the budget that node 1's pushforward leaves unused.
- `toms-overlap-window-cubes-force-linear-depth` is false for every `c > 1/2`: part 2 gives
  depth `N/2` for even `N`. The best possible constant is `c = 1/2`. The route
  `toms-leaf-average-rank-via-overlap-window-cubes` only needs some `c > 0`, and with
  `c = 1/2` it would give `eps_M >= 1/(4 d_n)`.
- Part 1 does not grow with `N`. The joint divisibility (the lcm of both leaf-maximum
  products over `prod_nu Y_nu`) has degree `N D + N > N D` and yields one drop, not `N/2`.
  It is a global statement, and part 2 shows that it is sharp at `N = 2`.

**Split-model evidence beyond split targets.** In the token model the node lines move
between bins with inter-node carries allowed, and a map into
`|K_d| = {sum floor >= T - d}` on a Kuhn-triangulated box is a SAT instance
(`token_depth.py`). The minimal depth is `1, 1, 2` for `N = 1, 2, 3` (grid `t = 1`). It is
UNSAT at depth `ceil(N/2) - 1` and SAT at depth `ceil(N/2)`. With closed walls (no gap
regions), the `N = 2` depth-1 instance becomes UNSAT (`token_sat.py`). So the staggering
uses exactly the lower semicontinuous fading at walls. SAT instances are realized by
depth-one transports, so they are genuine upper bounds. UNSAT instances are evidence only.
A general target need not split.

**Not settled.**
- A lower bound `c N` for general, non-split targets. A candidate is `ceil(N/2)`, via a
  pairing argument that bounds how many nodes can absorb their overlap.
- The non-integer variant `U = floor(N D)`.
- Windows with `kappa >= 2`, where one absorbing node costs `D + kappa`.
