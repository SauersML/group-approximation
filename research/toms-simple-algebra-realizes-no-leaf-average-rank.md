---
rg: 2
id: toms-simple-algebra-realizes-no-leaf-average-rank
kind: claim
title: In Toms's simple no-Gamma algebra B the leaf-average functions tau(h), h non-constant, are not ranks
distinct_from:
  toms-schubert-algebra-continuous-ranks-are-constant: that conjectures every continuous rank is constant; this asks only that the explicit leaf-average targets tau(h) are not ranks, the targets on which the Poincare-Miranda machinery acts.
  toms-schubert-algebra-misses-a-rank: that asks for some unrealized strictly positive continuous affine function; this names the candidates, and implies that claim through toms-schubert-algebra-misses-a-rank-via-leaf-average.
  toms-simple-algebra-has-no-block-diagonal-rank-realizer: that proves the claim for realizers that are block-diagonal from some stage on; this asserts it for all realizers.
---

**OPEN.** Let `B` be Toms's Proposition 4 algebra (arXiv:2606.12188v2), and
`h in C(X_1)` with `0 <= h <= 1` and `h` non-constant. Then no `a in (B tensor K)_+`
has `d_tau(a) = tau(h)` for every `tau in T(B)`.

The same statement for the non-simple limit `A` of Toms's Section 4 is the test case.

**Model test.**
- *Diagonal quotient.* On the diagonal quotient of `A` the conclusion fails.
  The uniformly distributed element realizes `tau(h)`
  (`toms-diagonal-quotient-has-nonconstant-continuous-ranks`), so the claim
  depends on traces with independent leaf coordinates.
- *Constant `h`.* For constant `h` the conclusion fails too, since projection
  sums realize constants.

## Attempts

- **Proved: rank counts never obstruct.**
  `toms-rank-bookkeeping-admits-monotone-realizer-profiles`. Any proof must use
  the operators implementing the Cuntz containments.
- **Proved: block-diagonal realizers do not exist.**
  `toms-simple-algebra-has-no-block-diagonal-rank-realizer`, and in `A`
  `toms-line-subalgebra-has-no-nonconstant-continuous-rank`. Along a product of
  paths, a robust Poincare–Miranda point makes half the top copies jump at
  once. So a realizer must, beyond every stage, carry support between top copies.
- **Proved: uniform carries are useless.**
  `toms-twisted-swap-pairs-are-totally-degeneracy-forcing`. A carry made the
  same way in all copies of a node loses the whole pushforward at one point.
- **The crux: copy-dependent carries.** A carry from copy `b` into copy `b'` has
  components that are sections of Hom bundles twisted by `gamma_(b') tensor gamma_b^*`,
  pulled back from the projective factors on the tree path joining `b` and `b'`.
- **Plan: twisted Poincare–Miranda.** Let the projective coordinates `p in P` vary
  together with the path product `t in [0,1]^K`. Combine the degree in `t` with the
  Thom–Porteous classes in `p` to find `(t*, p*)` where every carry that heals an
  aligned wall vanishes. The containment is then block-diagonal at `(t*, p*)`, and
  half the copies jump there.
- **Where the plan dies (2026-09-13).**
  - Without blockwise domination there are no per-copy lower semicontinuous
    counts, so the Miranda sets `V_b` are defined only on the zero locus of the
    carries, not on whole faces.
  - A carry through a single node factor `CP^(j_r)` can be spread over more than
    `j_r` sections with no common zero. Only carries through distinct factors
    are forced to vanish together, by Künneth.
  - A first sub-case to settle: carries of rank at most `sqrt(2) d_r` through one
    level-`r` node, where the swap theorem forces total degeneracy.
- **Calibration and a transport obstruction (sw-113, 2026-09-17).**
  - *Calibration.* `untwisted-doubling-tower-has-a-nonconstant-continuous-rank`
    shows that with trivial twists every leaf average is a rank. The realizer is
    averaged ramps, and its containments come from Robert's dimension-two
    comparison over a square. So the firewalls above are sharp, and any proof has
    to use the twists.
  - *Obstruction.* `toms-constant-rank-twisted-transport-costs-double-rank` shows
    that in `A` a containment whose target has constant rank on a swap family
    `{(x(s), x(1 - s))} x CP^j` needs rank at least twice the swapped rank. The
    proof counts roots of the total Chern class. Deep approximants of a realizer
    therefore cannot rotate support between top copies at constant rank, which is
    exactly the step the calibration uses. They must drop support on the swap
    family and pick it up again.
  - *Next.* Bound the drop loci. The same Chern count on a sub-slice where the rank
    is constant should force the drop set to have large dimension. Then run the
    argument in `B` with the point-evaluation blocks included.
- **Drop loci bounded, and the single-family route blocked (w3-113, 2026-09-17).**
  - *Drop-locus bound.* `toms-swap-drop-locus-has-codimension-at-most-2m-plus-1`
    shows that the Chern count survives a drop set `D` with `dim D <= 2j - 2m - 1`.
    The proof doubles the arc and uses Alexander duality. So a target of maximal
    rank `m < 2 max(R_x, R_y) + π` on a swap family drops rank on a set of dimension
    at least `2j - 2m`. In `A`, deep approximants drop on codimension at most
    `2 r_(M-1) + 1`.
  - *In `B`.* `toms-simple-algebra-approximants-drop-rank-on-a-large-set` runs the
    same bound through branch traces. The point blocks enter as a trivial summand
    and cancel, and the margin is `delta Delta`. Every finite-stage `a''` between a
    deep approximant and the band drops on dimension at least
    `delta^2 r_M^2 - 2 r_M/delta`.
  - *Blocked.* `toms-chern-swap-count-allows-depth-one-drops` builds a target
    `Q >= phi(a')` of the leaf profile on one swap family, with rank in `{R-1, R}`.
    It drops by one on `{c_i} x hyperplane`. Traces see these drops as `1/r_M`, so the
    drop count on one family plus the bands cannot reproduce the firewall's `K/2`
    jump. The step "combine with Poincare–Miranda" fails there.
  - *Next.* Try depth additivity across sibling doubling nodes. On the cube family
    `[0,1]^N x prod CP^(j')`, product models drop at a common point with depth `N`.
    Prove by Künneth that coordinated transports cannot stagger their drops across
    nodes, or build a staggered one. Depth `K/2` at one point would give the
    `delta/(2 r_n)` jump in `A` and `B`.
- **Two sibling nodes cannot stagger (w5-113, 2026-09-18).**
  - *Result.* `toms-two-sibling-swap-drops-add-to-depth-two`. Take a box of windows
    in the square family of two sibling swap nodes. Suppose the target contains a
    common bundle `G` plus, on each side, the transported line of that side's node,
    and has rank at most `rank G + 2`. Then it drops to `rank G` at an interior
    point.
  - *Proof idea.* Künneth alone is not enough, since depth-one drops kill every
    support-bundle count. The invariant is instead a degree-7 Mayer–Vietoris class
    of the space of matrices with rank in `{g+1, g+2}`. On the boundary loop it
    evaluates to `(alpha - beta)^2 (alpha + beta)(u_1 u_2^2 - u_1^2 u_2)`, which is
    non-zero for Toms's twists and zero untwisted.
  - *Scope.* The staggered depth-one model therefore drops by `2` in every window
    box, however the two nodes are coordinated. A depth-two drop is still only
    `2/r_M` on a trace. The invariant vanishes for `alpha = -beta`.
  - *Next.* Two steps remain.
    - The `N`-node box. Find a class of the band of width `N` that is non-zero on
      the boundary `S^(N-1) x prod CP^(j')` of the window box. The candidate is the
      iterated Mayer–Vietoris class over the cross-polytope loop of `2N` lines.
      This would force depth `N`.
    - Window extraction. Show that a general deep approximant has window boxes,
      starting from the drop sets of the single-node bound.
