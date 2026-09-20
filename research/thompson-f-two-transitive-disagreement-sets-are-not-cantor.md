---
rg: 2
id: thompson-f-two-transitive-disagreement-sets-are-not-cantor
kind: claim
title: In a 2-transitive action of Thompson's group F, no disagreement set of a pair has empty interior
distinct_from:
  thompson-f-two-transitive-disagreement-sets-have-no-interior: that claim excludes disagreement sets that contain an interval; this claim excludes the complementary case, disagreement sets that contain no interval, which are Cantor sets
  thompson-f-two-transitive-disagreement-sets-are-self-similar: that claim proves the shape restrictions (perfect, infinitely many components, a translate of each clopen piece); this claim excludes one of the two shapes left over
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. With the disagreement set `D(ω,ω')` as defined in
`thompson-f-two-transitive-disagreement-sets-are-self-similar`, the claim is
that `D(ω,ω')` has nonempty interior in `[0,1]` for some (equivalently, every)
pair `ω ≠ ω'`.

By the self-similar claim, all such sets are `F`-translates of one compact,
perfect set `D_0 ⊂ (0,1)`. A compact perfect subset of the line with empty
interior is a Cantor set, so the claim is: **`D_0` is not a Cantor set.**

This is one of the two halves of
`thompson-f-no-two-transitive-via-disagreement-set-type`. It is OPEN.

## Attempts

- 2026-09-18 (swarm-0917-w7-w7-z-break, minimal-counterexample). The set-up only.
  - If `D_0` is a Cantor set, then every nonempty clopen piece of `D_0` is an
    `F`-translate of `D_0`. So the germs of `F` must carry `D_0` onto each of
    its clopen pieces, piecewise linearly with dyadic data.
  - A natural test: take `D_0` to be the limit set of a finite family of
    elements of `F` contracting `D_0` onto its pieces. This is a
    self-similar Cantor set with dyadic affine maps. The middle-thirds set is
    not of this type because its ratios are `1/3`. Dyadic self-similar Cantor
    sets exist, for example the points whose binary digits in odd places are
    `0`.
  - Missing: an invariant of the pair `(ω,ω')` that is forced by 2-transitivity
    and cannot live on a Cantor set. One candidate is the germ formula
    `D(ω,gω) = g(B(g))`, where `B(g)` is the set of points at which the germ of
    `g` is not the germ of an element of the stabilizer `F_ω`. This is not
    written out.
- 2026-09-19 (swarm-0917-w14-w14-z-break, reframing): the orbit count on
  products over cuts. Proved in
  `thompson-f-two-transitive-cantor-case-orbit-counts`. Assume case (A) and
  take a good irrational orbit `O`.
  - `Ω` is a product over any finite set of good cuts, and disagreement sets
    add over the cuts.
  - `K = F_ω ∩ F_{ω'}` has exactly `b`, `ab` and `a` orbits on `O ∩ (0,ξ)`,
    on `O ∩ (ξ,η)` and on `O ∩ (η,1)`.
  - `H` has `m^{n-1}` orbits on increasing `n`-tuples of `O`.
  - So case (A) splits. In (A1), `m = 1`, which forces `a = b = 1`: `K` has
    three orbits on `O`, is transitive on the gaps of `D(ω,ω')`, and `H` is
    order-transitive on `n`-tuples of `O` for all `n`. In (A2), `m ≥ 2`.
  - Class kill: `E = 1/2 + C/4`, with `C` the points whose binary digits in
    odd places are `0`, passes every set-level test recorded so far. That
    covers F-self-similarity of clopen pieces, rational extreme points, and
    an element preserving `E` with slopes `4` and `1/4` at the two ends. So
    shape-only arguments are dead.
  - Where it stopped: refuting (A1). The natural route is to show that a
    subgroup `K ≤ F` preserving a Cantor set `D_0` cannot be transitive on
    its gaps while its germs at `ξ` and `η` sit in index-2 position (the swap
    germ is not in `L`, but its square is). This fails at the first step: an
    order-preserving PL group can be transitive on the gaps of a
    self-similar Cantor set, because the gap set has the order type of `Q`.
    For `E`, map the two clopen halves on either side of one gap onto those
    on either side of another, using Step 8 of the proof.
    No invariant separating the gap near `ξ` from the gap near `η` under `K`
    was found.
  - Refuting (A2) would need an upper bound on `m` from maximality of `H`.
    None is known.
- 2026-09-19 (swarm-0917-w15-w15-z-last1, calibration). Two new nodes, and the
  claim is still OPEN.
  - `thompson-f-two-transitive-gap-endpoints-lie-in-hull-orbits`: every left
    gap endpoint of a disagreement set lies in `Θ^-` and every right gap
    endpoint in `Θ^+`. Splicing at a point of the gap gives `α` with the two
    endpoints equal to `η(ω,α)` and `ξ(α,ω')`. In the Cantor case,
    `D_0 ∩ Θ^±` are dense in `D_0`.
  - `quaternary-cantor-set-passes-disagreement-shape-tests`: the example of
    the previous entry, `K = 1/2 + C/4` with `C` the base-4 digits-`{0,1}`
    set, satisfies all known shape conditions. Its orbit `F·K` is the finite
    disjoint unions of dyadic affine copies of `K`. It is closed under clopen
    pieces and disjoint unions. The minima of its members are dyadic, their
    maxima lie in `F·(1/3)`, and the gap endpoints are as required. Each member
    has a swap-like stabilizing element with slope `1/4` at both extreme
    points. So nothing that uses only `F·D_0` and the endpoint orbits can
    prove this claim.
  - Unproved, recorded only: "local transitivity", meaning that
    `D(ω,σ) ⊂ (p,q)` implies `σ ∈ F_{[p,q]} ω`, would give strong control of
    the `F_ω`-orbit of `D_0`. It is equivalent, circularly, to transitivity of
    `F_ω ∩ F_p^+` on `(F·t) ∩ (p,1)` for good irrational `t`. Both reduce to
    localizing germs of `F_ω`, and this step is not done.
  - Where it dies: the data a proof must use are not shape data. They are
    overlaps of `D(ω,·)` along an `F_ω`-orbit (the binary sum rule, where
    available, is the only known constraint), colourings with three or more
    colours, or the germ formula for `F_ω`. Next step: test the binary sum rule
    on `F·K`. If the Cantor case occurs,
    `{ D(ω,σ) : σ ≠ ω }` is a family of copies closed under closures of
    symmetric differences. Decide whether some such family, `F_ω`-invariant,
    can exist for `K`.
- 2026-09-19 (swarm-0917-w17-w17-z-last1, reframing). One new node, and the
  claim is still OPEN.
  - `thompson-f-two-transitive-colour-pairs-are-totally-mixed` covers any
    number of colours. Every ordered pair of distinct colours occurs between
    every pair of points. At every point component of a disagreement set,
    every colour pair is dense (two splicings reduce a missing pair to an
    empty `D^{ij}`). The set-wise stabilizer of any one colour `P` is already
    `F_ω`.
  - Reduction. In the Cantor case, `Ω ≅ F·P` as `F`-sets, and
    `D(aH,bH) = cl(aP ∖ bP) = cl(bP ∖ aP)`. So this claim follows from (†)
    in that node: no dense, codense `P` in an irrational orbit has a
    stabilizer that is transitive on `F·P ∖ {P}` together with equal,
    nowhere dense closures of the one-sided differences.
  - Kills: inclusion models (`fP ⊊ P`), one-way local moves, and every
    three-or-more-colour model with a missing colour pair near a point
    component.
  - Where it dies: the binary sum rule and injectivity of `σ ↦ D(ω,σ)` are
    still not available in the Cantor case. The step left is to exclude a
    subset `P` whose translates differ from it in a checkerboard pattern,
    with equal, nowhere dense one-sided difference closures. The converse of
    the reduction is not proved either, since it needs
    `D(P,fP) ⊂ cl(fP Δ P)`.
