---
rg: 2
id: locally-quasiconvex-hyperbolic-groups-have-no-type-a-actions
kind: claim
title: Surface groups, infinite locally quasiconvex hyperbolic groups and closed hyperbolic 3-manifold groups carry no type (A) action; in any hyperbolic group, type (A) point stabilizers of infinite orbits have full limit set
requires:
  - limit-set-escaping-forces-infinitely-many-double-cosets
  - hyperbolic-groups-have-fg-subgroups-with-two-double-cosets
distinct_from:
  type-a-actors-have-no-proper-power-cyclic-edge-splittings: that excludes actors with an irreducible splitting over a finite group (so free and all infinitely-ended hyperbolic groups) or over a proper-power cyclic piece; this excludes one-ended hyperbolic actors such as surface groups and closed hyperbolic 3-manifold groups, which split only over non-proper-power cyclic groups or not at all.
  hyperbolic-groups-have-fg-subgroups-with-two-double-cosets: that shows finitely generated subgroups with two double cosets exist in hyperbolic groups when they need not be core-free; this shows faithfulness plus local quasiconvexity, or a 3-manifold structure, rules them out.
  ascending-baumslag-solitar-groups-have-no-type-a-action: that is another single-class exclusion of the same shape, for a non-hyperbolic class.
---

**ESTABLISHED** (lane proof; not reviewed; no priority claimed).
- **Definition used.** A type (A) action is as on main: a faithful action with
  finitely generated point stabilizers and finitely many orbits of two-element
  subsets.
- **Cited inputs, not read at source this session:**
  - An infinite-index quasiconvex subgroup of a hyperbolic group has limit set a
    proper closed subset of `∂G`.
  - Double density of loxodromic fixed pairs in non-elementary hyperbolic
    groups.
  - Local quasiconvexity of surface groups.
  - For item 3: tameness (Agol; Calegari–Gabai), Canary's covering theorem, and
    Thurston's dichotomy for closed hyperbolic 3-manifolds. Every finitely
    generated infinite-index subgroup is either convex cocompact (quasiconvex)
    or has a finite-index subgroup that is the fiber group of a fibration of a
    finite cover over the circle.

**Statement.** Let `G` be a non-elementary hyperbolic group.
1. **Full limit set.** If `H ≤ G` has finitely many double cosets, then
   `Λ_H = ∂G`. So in any type (A) action of `G`, the stabilizer of a point with
   infinite orbit is finitely generated, has infinite index, is not
   quasiconvex, and has full limit set.
2. **Locally quasiconvex groups.** If `G` is locally quasiconvex, then `G` has no
   type (A) action. This includes surface groups of genus `≥ 2`, which are not
   covered by the splitting obstructions on main.
3. **Closed hyperbolic 3-manifold groups.** If `G = π_1(M)` with `M` a closed
   hyperbolic 3-manifold, then `G` has no type (A) action.
4. **Conditional, all hyperbolic groups.** Suppose `G` has trivial finite
   radical, and every finitely generated subgroup of `G` with full limit set has
   finite index or contains a nontrivial normal subgroup of `G`. Then `G` has no
   type (A) action.

**Proofs.**
- **Item 1.** Limit sets are closed, since `G` acts properly. If `Λ_H ≠ ∂G`,
  double density gives a loxodromic with both fixed points in `∂G∖Λ_H`. Then
  `limit-set-escaping-forces-infinitely-many-double-cosets` applies. For a type
  (A) action, each orbit `G/H_i` has finitely many pair orbits, so `H_i\G/H_i`
  is finite. If the orbit is infinite, `H_i` has infinite index, and item 2 of
  the calibration node excludes quasiconvex `H_i`.
- **Setup for items 2–4.** A type (A) action has finitely many point orbits
  `G/H_1, …, G/H_r`. Its kernel `⋂_i core(H_i)` is trivial by faithfulness.
- **Item 2.** Every `H_i` is finitely generated, hence quasiconvex. So by item 1
  every orbit is finite, and every `H_i` has finite index. The kernel is then
  an intersection of finitely many finite-index subgroups. So faithfulness forces
  `G` to be finite, which is a contradiction.
- **Item 3.**
  - **Fiber stabilizers.** By item 1 and the dichotomy, each `H_i` with infinite
    orbit has a finite-index subgroup `F_i ⊴ G'_i` with `G'_i/F_i ≅ Z` and
    `[G:G'_i] < ∞`.
  - **A common subgroup.** Let `G_2` be a normal finite-index subgroup of `G`
    contained in every `G'_i` and in every `H_j` with finite orbit.
  - **Each core is big.** For every `g`, `gF_ig⁻¹ ∩ G_2` is normal in `G_2`, and
    the quotient embeds in `Z`. Only finitely many conjugates occur, since
    `N_G(F_i) ⊇ G'_i`. So `core(H_i) ⊇ core(F_i) ⊇ [G_2,G_2]`. The same
    inclusion holds for finite orbits, since there `G_2 ⊆ H_j`.
  - **Contradiction.** So the kernel of the action contains `[G_2, G_2]`, which
    is nontrivial because `G_2` is non-elementary hyperbolic, hence non-abelian.
    This contradicts faithfulness.
- **Item 4.**
  - **Normal subgroups in the cores.** By item 1 each `H_i` with infinite orbit
    has full limit set, so by hypothesis `H_i` contains a nontrivial normal
    `N_i ⊴ G`. For finite orbits take `N_i = core(H_i)`, of finite index. Then
    `N_i ⊆ core(H_i)`.
  - **Infinite and non-central.** With trivial finite radical, each `N_i` is
    infinite, so it contains a loxodromic. Two infinite normal subgroups `N, N'`
    have `[N, N'] ≠ 1`. Otherwise `N` would centralize a loxodromic `b ∈ N'`,
    so `N` would lie in the virtually cyclic `E(b)`. Then `N` would be an
    infinite virtually cyclic normal subgroup of a non-elementary group, which
    is impossible.
  - **Contradiction.** By induction `⋂_i N_i ⊇` an iterated commutator, and that
    is `≠ 1`. So the action is not faithful.

**Consistency with BBMZ.** BBMZ realize hyperbolic groups inside contracting
rational similarity groups. The finitely generated stabilizers of rational points
there are subgroups of the host, not of `G`. In `G`'s own boundary action, point
stabilizers are finite or virtually cyclic, hence quasiconvex, so by item 1 those
orbits have infinitely many pair orbits. No conflict.

**What is open.**
- **The hypothesis of item 4.** Does every finitely generated subgroup with full
  limit set have finite index or contain a nontrivial normal subgroup? This lane
  does not know it in general. It holds for 3-manifold groups by tameness, as
  item 3 shows, and trivially in locally quasiconvex groups.
- **The core-free question.** A finitely generated, core-free, infinite-index,
  double-coset-finite subgroup of a hyperbolic group would have to be a
  counterexample to that hypothesis.

## Attempts

1. **One pass at the hypothesis of item 4 (bh-free-40, 09-18).** Not decided.
   - **A weaker hypothesis suffices.** Suppose `H_0 ≤ H` has finite index,
     `H_0` is infinite, and `H_0 ⊴ G_0` with `[G:G_0] < ∞`. Then
     `core_G(H) ≠ 1`, with no abelian-quotient assumption.
     - Take `G_2 ⊴ G` of finite index inside every conjugate of `G_0`. Then
       each `gH_0g⁻¹ ∩ G_2` is an infinite normal subgroup of `G_2`, and only
       finitely many occur.
     - In a non-elementary hyperbolic group, two infinite normal subgroups `N`
       and `N'` contain independent loxodromics `a` and `b`. Then
       `[a^m, b^m] ∈ [N, N']` has infinite order for large `m` (ping-pong), so
       `[N, N']` is infinite normal.
     - By induction, the finite intersection is infinite, and it lies in
       `core_G(H)`.
     - So item 4 holds under this assumption: every finitely generated subgroup
       with full limit set is virtually an infinite normal subgroup of a
       finite-index subgroup, or has finite index. Trivial finite radical is not
       needed for this form. Item 3 is its instance given by tameness.
   - **Where a counterexample must live.** It must be finitely generated, with
     full limit set, and virtually contain no infinite normal subgroup of any
     finite-index subgroup. So it must be neither quasiconvex nor of
     virtual-fiber type.
   - **What was tried.**
     - Subgroups of a Rips kernel `N ⊴ G` would need a Cannon–Thurston image
       covering `∂G`.
     - Invariant free factors in reducible atoroidal free-by-cyclic groups
       produce subgroups that are normal in a smaller free-by-cyclic group. Their
       limit set is that subgroup's, which is not full.
     - Kernels of maps to `Z` in higher-dimensional hyperbolic groups are normal.
   - **Literature.** Bounded arXiv searches found no statement either way. The
     general hyperbolic case stays OPEN.
