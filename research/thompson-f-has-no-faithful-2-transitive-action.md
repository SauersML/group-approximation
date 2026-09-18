---
rg: 2
id: thompson-f-has-no-faithful-2-transitive-action
kind: claim
title: Thompson's group F has no faithful 2-transitive action
distinct_from:
  thompson-f-admits-a-faithful-2-transitive-action: that claim is the affirmative answer to Problem 2.20; this claim is its negation, i.e. td(F) = 1
---

Every action of Thompson's group `F` on a set `Ω` with `|Ω| ≥ 3` fails to be
transitive on ordered pairs of distinct points. By
`thompson-f-two-transitive-actions-are-faithful`, faithfulness is automatic,
so this says the transitivity degree of `F` is 1.

## Attempts

- 2026-09-13 (z2-20-f-2-transitive). Suppose `F` acts 2-transitively on `Ω`.
  For an open interval `U ⊂ (0,1)`, `F_U^c` denotes the elements with compact
  support in `U`.
  - **Case I: some `F_U^c` fixes a point. Dead.** The complement `C_ω` of the
    union of intervals whose `F_U^c` fixes `ω` is an equivariant, nonempty,
    proper closed set. Pushing a gap endpoint makes the extreme point of
    `C_ω Δ C_{gω}` lie on one side only, an antisymmetric invariant relation.
    Recorded as `thompson-f-two-transitive-rigid-stabilizers-fix-no-point`
    (unreviewed).
  - **Case II: no `F_U^c` fixes a point. Open.** Every `F_U^c` acts on `Ω` with
    all orbits infinite. The grid condition
    (`thompson-f-two-transitive-actions-satisfy-grid-condition`) holds at every
    `x`. Every unordered pair `{ω,ω'}` then gets an equivariant hull `[η,ξ]`:
    `ω' ∈ O_x^-(ω)` iff `x` is right of `ξ`, and `ω' ∈ O_x^+(ω)` iff `x` is
    left of `η`. This is well defined by the grid condition, and hulls satisfy
    an ultrametric-type inequality. An element swapping `ω, ω'` fixes both
    `η` and `ξ`. Missing: an antisymmetric invariant attached to a hull
    endpoint, or a proof that point stabilizers are confined. Confined
    stabilizers, via the commutator lemma of Le Boudec–Matte Bon
    (arXiv:2006.08677 Theorem 3.17, restated as arXiv:2012.03997 Theorem 3.5),
    would put some `F_U^c` in a stabilizer and so reduce to Case I.
  - Candidates that Case II allows and that must be killed or realized:
    stabilizers of dense subsets or of partitions of an `F`-orbit
    (Golan–Sapir's maximal subgroups; Jones' subgroup).
- 2026-09-17 (swarm-0917-w4-pull-z-4, reframing: hull endpoints as two
  ultrametrics). **Partial; the node stays open.**
  - Proved `thompson-f-two-transitive-hull-endpoints-are-separated`:
    - `η` is an equivariant ultrametric (the largest value in a triple is
      attained twice);
    - `ξ` is an ultrametric for the reversed order (the smallest value is
      attained twice);
    - `ξ < η` strictly on every pair. If `ξ = η` held on one pair, it would hold
      on all pairs, which forces a constant value and so an `F`-fixed point.
  - Kills every model with a pair that disagrees at a single point of `(0,1)`.
  - Proposed reduction of the kind-2 case of
    `thompson-f-two-transitive-dyadic-branching-is-binary` (sketch only, not
    written as claims):
    - With `P_ω` the dyadic orbit, a stabilizer should be the stabilizer of a
      subset `ψ` of the dyadics under the Jones affine action
      `g⋆E = gE Δ J_L(g)` (`jones-subgroup-cosets-form-a-parity-lamplighter`).
    - The differences `E_1 Δ E_2` push forward as a cocycle.
    - If a difference is finite, or a finite union of intervals, the model dies
      by counting: disjoint sets `A`, `B` and `A ∪ B` would all lie in one
      orbit.
    - Missing: kind 1, and kind 2 with differences that have infinitely many
      components.
  - Also found: twisted models defeat the T1-type antisymmetric tests of
    `thompson-f-admits-a-faithful-2-transitive-action`.
- 2026-09-18 (swarm-0917-w7-w7-z-break, minimal-counterexample: disagreement
  sets of pairs). **Partial; the node stays open.**
  - Proved `thompson-f-two-transitive-disagreement-sets-are-self-similar`
    (unreviewed). For `ω ≠ ω'`, let `D(ω,ω')` be the set of `x` at which no
    element that is the identity near `x` sends `ω` to `ω'`. Then:
    - all these sets form one `F`-orbit of compact subsets of `(0,1)`;
    - their extreme points are `ξ` and `η`;
    - disjoint `D(ω,ω')`, `D(ω,ω'')` force `D(ω',ω'') = D(ω,ω') ⊔ D(ω,ω'')`;
    - splicing at a gap realizes every clopen piece as a disagreement set, so
      every nonempty clopen piece of `D_0` is an `F`-translate of `D_0`;
    - an `F_U^c` element beside `D_0` makes `D_0` disconnected.
  - So `D_0` is perfect, with infinitely many components, none relatively open.
  - Kills every model in which some pair has a disagreement set with finitely
    many components. This covers the finite-difference and finite-interval-union
    models of the 2026-09-17 entry, kind 1 and kind 2 together, with no affine
    reduction.
  - Split of what is left, route
    `thompson-f-no-two-transitive-via-disagreement-set-type`:
    - `thompson-f-two-transitive-disagreement-sets-are-not-cantor` (OPEN);
    - `thompson-f-two-transitive-disagreement-sets-have-no-interior` (OPEN).
- 2026-09-18 (swarm-0917-w8-w8-z-follow, reframing: colourings of irrational
  orbits). **Partial; the node stays open.**
  - Proved `thompson-f-two-transitive-irrational-orbit-colorings`
    (unreviewed). At an irrational `y` the germ group is trivial, so
    `F_y = G_y` and the local stalk `Ω/G_y` is `H\F·y`. So agreement of two
    points at `y` is equality of `H`-orbit labels, and `Ω` embeds
    equivariantly into colourings of any irrational orbit that meets `D_0`.
    There are uncountably many such orbits.
  - Consequence: every point stabilizer `H` is the part-wise stabilizer of
    its own orbit partition of an irrational orbit, with at least two dense
    parts. So Problem 2.20 is exactly the Le Boudec–Matte Bon
    partition-stabilizer question, restricted to irrational orbits.
  - The two open halves become statements about `H` alone. By Baire category,
    `D_0` is Cantor iff `H` is transitive on some irrational orbit (then on a
    comeagre set of them). `D_0` has interior iff `H` is transitive on none.
    Equivalently:
    - `...-are-not-cantor` says no `H` satisfies `F = H·F_y` for an
      irrational `y`;
    - `...-have-no-interior` says every `H` satisfies it for some `y`.
  - In the Cantor case, at every good irrational `y`, `Ω = Ω/B_y × Ω/A_y` and
    `H ∩ G_y = (H ∩ A_y) × (H ∩ B_y)`, where `G_y = A_y × B_y` is the product
    of the left and right parts.
  - Missing: a proof that `F = H·F_y`, with `F_y = A_y × B_y`, is incompatible
    with two double cosets, or that it is forced.
