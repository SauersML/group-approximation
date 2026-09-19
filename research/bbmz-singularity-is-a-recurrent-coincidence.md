---
rg: 2
id: bbmz-singularity-is-a-recurrent-coincidence
kind: claim
title: In a BBMZ horofunction host, an element is singular only over the fibers of its offset frontier, and over a frontier point it is singular exactly when two kinds of atom splitting coincide at infinitely many depths (in right-angled Coxeter groups, a wall crossing the frontier wall and a wall that does not); in every hyperbolic group the singular set is the set of points whose pair-type path in a finite graph visits a finite set infinitely often, so it is countable or of the size of the continuum, decided by a finite graph
requires:
  - hyperbolic-cone-matching-holds-off-the-branch-locus
  - horofunction-atom-configurations-have-finitely-many-types
  - k-local-distance-functions-on-hyperbolic-groups-are-global
  - busemann-frontiers-separate-the-boundary
distinct_from:
  bbmz-hosts-with-higher-dimensional-boundary-are-unbounded: that sketches singularity along wall spheres of reflections; this proves the exact criterion (recurrent coincidence) in right-angled Coxeter groups, shows frontier membership alone does not give it, and proves a general finite-graph description of singular sets.
  busemann-frontiers-separate-the-boundary: that proves the shear frontier separates and poses persistence; this proves the inclusion of singular sets in frontier fibers and replaces persistence by a decidable coincidence condition.
  hyperbolic-cone-matching-holds-off-the-branch-locus: that proves regularity off the branch locus with a fixed level shift; Theorem A here weakens the hypothesis to a single offset value on the fiber.
---

**Status.**
- **ESTABLISHED (lane proof, bh-q12-kazhdan, 2026-09-19; Referee bh-ref-q12 2026-09-19: Lemma B, Proposition C, Theorem D and Theorem E PASS, with a repair to the uncountability criterion; Theorem A checked only in its changed step):** Theorem A, Lemma B, Proposition C,
  Theorem D.
- **ESTABLISHED modulo BBMZ as stated:** Theorem E. It uses BBMZ (arXiv:2309.06224) `prop:MakeMorphisms` and
  `rem:SelfSimilarTree`, as `horofunction-atom-configurations-have-finitely-many-types` does.
- **OPEN:** Conjecture U for Kazhdan groups. Its uncountable form is now a finite condition, but that condition was
  not computed for any Kazhdan group.
- No computation was run, and no priority is claimed. Theorem E is the RSG analogue of Sidki's circuit dichotomy for
  finite-state tree automorphisms (polynomial versus exponential activity).

## Setting and notation

- `G` is hyperbolic with finite generating set `S`, `∂_h G` is its horofunction boundary, and `φ : ∂_h G → ∂G` is
  the Webster–Winchester map. Horofunctions are normalized by `η(1) = 0`. In the host application, `G` is `Γ ∗ Z`.
- **Atoms.** `Z_m(σ)` is the shadow of the infinite `B_m`-atom containing `σ ∈ ∂_h G`. `E_n(σ)` is the shadow of
  the `gB_n`-atom containing `σ`, i.e. `E_n(σ) = g ∂D` for the `B_n`-atom `D` of `g^{-1}σ`. Shadows of one level
  partition `∂_h G`.
- **Regular and singular points.** `y` is *regular* for `g` if there is `n_0` such that `g∂D` is the shadow of an
  infinite atom (of some level) for every `n ≥ n_0` and the `B_n`-atom `D` of `y`. This says the local actions of `g`
  along `y` are eventually surjective, in the nucleus language of the cone-matching node. `sing(g)` is the set of
  points that are not regular.
- **Offsets.** `ℓ_g(η) = η(g) − η(1)`, locally constant on `∂_h G`, with values in `[−|g|, |g|]`. The
  **offset frontier** `F'_g ⊆ ∂G` is the set of points whose fiber carries at least two values of `ℓ_g`.
  - It is closed: a finite union of sets `φ(ℓ_g^{-1}(c)) ∩ φ(ℓ_g^{-1}(c'))`.
  - It contains the sign frontier of `busemann-frontiers-separate-the-boundary` (for `g^k`).
- `f(v) = d(g,v) − d(1,v)` for `v ∈ G`.

## Theorem A (singular sets lie over the offset frontier)

`sing(g) ⊆ φ^{-1}(g^{-1} F'_g)`. More precisely, suppose `ℓ_g` takes a single value `b` on `φ^{-1}(gφ(y))`. Then
`g` maps all sufficiently deep atoms around `y` onto atoms of level `n − b`.

*Proof.* This is Theorem 1 of `hyperbolic-cone-matching-holds-off-the-branch-locus`, with one change in Step 1.
- There, `z_m ∈ W_m` with `f(z_m) ≠ b` accumulate at some `η ∈ φ^{-1}(gξ)`, and `f(z_m) → ℓ_g(η)`.
- Uniqueness of the fiber point was used only to conclude `ℓ_g(η) = b`. The present hypothesis gives that
  directly.
- Steps 2–4 do not use the fiber. ∎

**Consequence.** Singularity is confined to fibers over `g^{-1}F'_g`.
- For free groups on a basis, `F'_g = ∅`.
- For a standard generator `s` of a right-angled Coxeter group, `f = ±1` according to the side of the wall `H_s`,
  so `F'_s ⊆ ∂H_s`.

## Lemma B (front inequality; conical intrusion)

1. **Front inequality.** If `ℓ_g(η) = c`, then:
   - `argmin_{B_m} η ⊆ {f ≥ c}`;
   - `argmin_{gB_n} η ⊆ {f ≤ c}`.
2. **Conical intrusion.** If `ζ ∈ F'_g` carries values `a > b`, let `γ` be a geodesic ray from `1` to `ζ`. Then for
   all large `t`, the ball `B_R(γ(t))`, with `R = 8δ + 2|g| + 2`, meets both `{f ≥ a}` and `{f ≤ b}`.

*Proof.*
1. **Front inequality.**
   - For `v ∈ argmin_{B_m} η` we have `η(v) = −m = −|v|`. Since `η` is 1-Lipschitz,
     `d(g,v) ≥ η(g) − η(v) = c + |v|`.
   - For `v ∈ argmin_{gB_n} η` we have `η(v) = c − n` and `d(g,v) = n`. Then `d(1,v) ≥ −η(v) = n − c`.
2. **Conical intrusion.** By parts (0)–(2) of `k-local-distance-functions-on-hyperbolic-groups-are-global`
   (refereed), every point has a descending geodesic ray for each horofunction, converging to its `φ`-image.
   - Take the descending ray `β` of `η_a` from `1`, and the descending ray `α` of `η_b` from `g`.
   - Along `β`, and along `α`, the computation of part 1 gives `f ≥ a` on `β` and `f ≤ b` on `α`.
   - Both rays converge to `ζ`. Rays with a common endpoint are eventually `8δ`-close up to a time shift of at most
     `|g|` (Bridson–Haefliger III.H.3.3, recalled). ∎

So a frontier is always *conically* two-valued, i.e. the intrusion the persistence step asked for is automatic. What
is not automatic is singularity, as Theorem D shows.

## Proposition C (finite reduction)

For every `σ` and every `n ≥ |g|`,

`Z_{n+|g|}(σ) ⊆ E_n(σ) ⊆ Z_{n−|g|}(σ)`.

Hence `g^{-1}σ` is regular exactly when, for all large `n`, `E_n(σ) = Z_k(σ)` for some `k ∈ [n−|g|, n+|g|]`.

*Proof.*
- `B_{n−|g|} ⊆ gB_n ⊆ B_{n+|g|}` by the triangle inequality. Agreement modulo constants on a larger set implies
  agreement on a smaller one, which gives both inclusions.
- If `E_n(σ) = Z_k(σ)` with `k` outside the range, the inclusions force equality with `Z_{n∓|g|}(σ)`. ∎

## Theorem D (right-angled Coxeter groups: singularity is a recurrent coincidence)

**Setting.**
- `W` is a hyperbolic right-angled Coxeter group with its standard generators, so the Cayley graph is the 1-skeleton
  of the Davis cube complex and `d(u,v)` is the number of walls separating `u` and `v`.
- The *depth* of a wall is `δ_1(W) = d(1, W^{¬1})`, where `W^{¬1}` is the halfspace not containing `1`. Likewise
  `δ_g(W) = d(g, W^{¬g})`.
- Fix `g`, a wall `W_0` separating `1` and `g`, the reflection `r_0` in `W_0`, and `ζ ∈ ΛW_0` *generic*: `ζ` lies in
  no `ΛW''` for walls `W'' ≠ W_0` separating `1` from `g` or `1` from `r_0`.
- Let `σ_+` be a horofunction over `ζ` on the `1`-side of `W_0`, and `a = ℓ_g(σ_+)`.
- A deep wall near `ζ` is:
  - a *crossing wall* if it crosses `W_0`;
  - a *(+)-wall* if its far halfspace lies on the `1`-side of `W_0`;
  - a *(−)-wall* if its far halfspace lies on the other side.

**Claim.** `g` is singular at `g^{-1}σ_+` iff for infinitely many `N` both of the following hold:
- (i) some crossing wall of depth `N` cuts `Z_{N−1}(σ_+)`;
- (ii) some (+)-wall of depth `N` cuts the cylinder obtained from `Z_{N−1}(σ_+)` by adding the constraints of all
  crossing walls of depth `N`.

The same holds for the point `σ_−` on the far side, with the (+)-walls replaced by (−)-walls and the two
conditions in the opposite order.

*Proof.*
1. **Atoms are cylinders.**
   - `d(x,b) − d(x,1)` is a sum of `±1` over the walls separating `1` and `b`, signed by the side of `x`.
   - A wall separates two points of `B_m` iff it has depth `≤ m`. A geodesic from `1` crosses it by an edge inside
     `B_m` that is dual to it alone.
   - So two points lie in the same `B_m`-atom iff they lie on the same side of every wall of depth `≤ m`.
   - A horofunction is the same thing as a limit orientation of all walls. It is determined by its differences
     across edges, and those are constant on the edges dual to one wall.
   - So `Z_m(σ)` is the set of points agreeing with `σ` on all walls of depth `≤ m`. Translating by `g`, `E_n(σ)` is
     the set agreeing with `σ` on all walls with `δ_g ≤ n`.
2. **Offsets near generic `ζ`.**
   - Walls separating `1` from `g` are quasiconvex. For every one of them except `W_0`, deep halfspaces near `ζ`
     (convex, hence visually small) lie on one side.
   - So `f` takes only two values near `ζ`: `a` on the `1`-side of `W_0` and `a − 2` on the other.
   - Hence `δ_g = δ_1 + a` for (+)-walls and `δ_g = δ_1 + a − 2` for (−)-walls.
   - For a crossing wall `W`, `r_0` commutes with the reflection in `W` and preserves the halfspaces of `W`. It maps
     the `1`-side part of `W^{¬1}` onto the other part.
   - Near `ζ`, `d(1, r_0 v) = d(r_0, v) = d(1,v) + 1` for `v` on the `1`-side. Here `f_{r_0}` takes the values `±1`,
     by genericity and `f_{r_0}(r_0 v) = −f_{r_0}(v)`.
   - So the far part on the other side is exactly one step deeper, and `δ_g = δ_1 + a − 1`.
3. **Which walls matter.** Deep cylinders at `σ_+` lie on the `1`-side of `W_0`, so (−)-walls never cut them. Walls
   far from `ζ` or of small depth are constraints in both families, or cut nothing.
4. **The sandwich.** Put `n = N + a − 1`. By step 2, `E_n(σ_+)` is the cylinder of (+)-walls of depth `≤ N−1` and
   crossing walls of depth `≤ N`. So `Z_N(σ_+) ⊆ E_n(σ_+) ⊆ Z_{N−1}(σ_+)`, and by Proposition C's argument only
   these two can equal it.
   - `E_n = Z_{N−1}` iff no crossing wall of depth `N` cuts `Z_{N−1}`. This is the negation of (i).
   - `E_n = Z_N` iff no (+)-wall of depth `N` cuts `E_n`. This is the negation of (ii).
5. **Two cylinders coincide iff no wall in one family and not the other cuts the other's cylinder.** This is
   immediate from the description as cylinders. So `E_n` is an atom iff (i) or (ii) fails, and singularity means
   both hold for infinitely many `n`. ∎

**Calibration (right-angled pentagon, `g = s`).** Checked by hand.
- The strip of chambers along `W_s` has, at every chamber `v` at distance `j`, the crossing wall to the next chamber
  and an outer wall of `v`.
- Both have depth `j + 1`, since both lie beyond all `j` walls separating `1` from `v`, and both cut.
- So (i) and (ii) hold at every depth, on both sides of both endpoints. That gives 4 singular chains, matching the
  computed ones (`gq-bh-finf-hyp-pentagon-three-checks.md`).

**What Theorem D shows about persistence.** If along `σ_+` the depths of the two kinds of event are eventually
disjoint, then `g` is **regular** at `g^{-1}σ_+`. Its level shift then alternates between `a` and `a − 1`.
- The offset frontier guarantees that both kinds of wall exist near `ζ`: Lemma B, and crossing walls whenever `W_0`
  is crossed.
- It does not guarantee that they coincide.
- So persistence is a statement about **recurrent coincidence**, not about frontier membership. No example of a
  frontier point with only finitely many coincidences was found.

## Theorem E (singular sets are Büchi sets of a finite graph)

**Pairs.** For `n ≥ |g|`, put `P_n(σ) = (Z_{n−|g|}(σ), E_n(σ))`. By Proposition C, the second entry lies inside the
first.

**Pair types.** Two pairs have the same type if one `ℓ ∈ G` is simultaneously:
- a morphism of the first atoms (BBMZ `def:morphisms`);
- a morphism of the second atoms in the `g`-translated tree, i.e. `g^{-1}ℓg` is a morphism of `g^{-1}E`.

1. **There are finitely many types.**
   - The fronts of both atoms lie within bounded distance `R(δ, |g|)` of `γ(n − |g|)`. For the first atom this is
     item 1 of the configuration theorem; for the second, it is the same item for `g^{-1}E` translated by `g`.
   - A joint signature consists of the two front neighborhoods, `σ` on their union modulo one constant, and the cones
     relative to `1` and relative to `g`. It ranges over finitely many classes (Cannon's cone types).
   - Equivalent joint signatures give the two morphisms, by `prop:MakeMorphisms` applied twice.
2. **The type decides whether `E_n(σ)` is an atom shadow.** By Proposition C, it is one iff it equals a descendant of
   `Z_{n−|g|}(σ)` at relative depth `≤ 2|g|`. Morphisms carry descendants to descendants at the same relative depth.
3. **The type decides the multiset of child types.** Morphisms map children to children and are morphisms between
   them (`rem:SelfSimilarTree`), and they preserve the nonemptiness of shadow intersections.
4. **Paths are points.**
   - An infinite path of child pairs has nested nonempty compact intersections, so it contains a point whose pairs
     are exactly the path.
   - Distinct paths separate at some step into disjoint shadows.

**Conclusion.** Let `T_sing` be the set of types whose `E` is not an atom shadow. Then `sing(g)` corresponds
bijectively to the paths of the finite pair graph `𝒢_g` that visit `T_sing` infinitely often. Consequently:
- `sing(g)` is either countable or of cardinality `2^{ℵ_0}`;
- it is uncountable iff some type in `T_sing`, reachable from a level-`|g|` root type, lies in a **nontrivial**
  strongly connected component of `𝒢_g` that is not a single simple cycle, counting parallel edges. (Corrected per
  the referee: trivial components, a single vertex without a loop, are visited at most once and do not count.)

This is a finite check once `𝒢_g` is built. Building `𝒢_g` is a finite computation from the BBMZ data (joint
signatures in a ball of radius about `R + 2|g|`, Cannon's cone types, and the morphism test). Its effectiveness is
expected but not verified here.

## Consequence for the Kazhdan program

- **Conjecture U, uncountable form.** For a Kazhdan hyperbolic `Γ`, some generator `s` of `Γ ∗ Z` has a `T_sing` type, reachable
  from a root type, in a nontrivial strongly connected component of `𝒢_s` that is not a single simple cycle.
  - By Theorems A and E, this is the whole content.
  - Frontier separation (uncountable `F'_{g^k}`) puts continuum-many points over the region where singularity is
    possible. It does not place a `T_sing` type in their components.
- **Decidable, not decided.** Deciding it for one explicit Kazhdan group, e.g. a uniform lattice or a Żuk group, is
  a finite computation. It needs the atoms of balls of radius about `R + 2|g|`. It was not run.
- **If it fails** (every reachable nontrivial component meeting `T_sing` is a single simple cycle), every singular set is countable. Bounded then needs
  only finitely many entry paths, a second finite check.
  - That would be the first real hope for a bounded, hence (by the refereed level-set theorem, once `C_r` holds)
    `F_∞`, host of a Kazhdan group.
- **If it holds,** the hidden data of a germ complex are the finitely many singular pair types. A finiteness theorem
  with colors equal to pair types (a Thumann operad on `𝒢_s`) is the natural next target. Whether its spine is
  finite is open.

## Lesson for general BH

- **Singularity is recurrence, not position.** An element fails to be finitary at a point exactly when two different
  splitting events of the atom trees, seen from `1` and from `g`, coincide at infinitely many depths.
- **Topology cannot give that.** It says where both events can occur (the offset frontier), not whether they occur
  together. The latter is a Büchi condition on a finite graph, so boundedness of a germ host is decidable in
  principle and has a countable/continuum dichotomy.
- **For BH hosts in general**, "bounded versus unbounded" should be read off a finite type graph of paired local
  pictures, not argued from the dimension or separation of the boundary.

## Referee (bh-ref-q12, 2026-09-19): B, C, D, E PASS; one repair to the criterion in Theorem E

**Theorem A.** Only the changed step was checked. The single-value hypothesis replaces fiber uniqueness in
Step 1 of `hyperbolic-cone-matching-holds-off-the-branch-locus`, Theorem 1. Steps 2–4 of that node were not
re-reviewed here.

**Lemma B: correct.**
- Front inequality. Descending rays give `min_(B_m) η = −m` and `min_(gB_n) η = c − n`. Then the 1-Lipschitz
  bound gives `f ≥ c` and `f ≤ c`, respectively.
- Conical intrusion.
  - The descending ray `β` of `η_a` from `1` lies in the argmin sets, so `f ≥ a` on it.
  - The descending ray `α` of `η_b` from `g` gives `f ≤ b` on it.
  - Both rays converge to `ζ` (refereed k-local node). Rays to a common endpoint are eventually `8δ`-close after a
    shift of at most `|g|`.

**Proposition C: correct.** `B_(n−|g|) ⊆ gB_n ⊆ B_(n+|g|)`, and atoms of a larger set are finer.

**Theorem D: correct, checked step by step.**
- *Cylinders.*
  - A wall separates two points of `B_m` iff its depth is `≤ m`.
  - An edge dual to a wall of depth `k ≤ m` lies inside `B_m`, so orientations of walls of depth `≤ m` are exactly
    what the `B_m`-atoms see.
- *Offsets.*
  - Genericity leaves `W_0` as the only wall separating `1` from `g` with `ζ` in its limit set. So `f ∈ {a, a−2}`
    near `ζ`.
  - (+)-walls have `δ_g = δ_1 + a`, and (−)-walls have `δ_g = δ_1 + a − 2`.
  - Crossing walls.
    - `r_0` commutes with the crossing reflection and preserves both halfspaces, because `W_0` meets both.
    - Genericity for the pair `(1, r_0)`, together with `f_(r_0) ∘ r_0 = −f_(r_0)`, forces the values `±1`.
    - So the other-side part of the far halfspace is exactly one step deeper, and `δ_g = δ_1 + a − 1`.
- *Classification of cutting walls: complete.*
  - A deep wall disjoint from `W_0` whose far halfspace contains `W_0` separates `1` from `g`, so it is one of
    finitely many, of bounded depth.
  - Every other deep wall near `ζ` is crossing, (+) or (−).
  - (−)-walls never cut cylinders on the `1`-side.
- *The sandwich.*
  - With `n = N + a − 1`, `E_n` is the cylinder of the (+)-walls of depth `≤ N−1` and the crossing walls of depth
    `≤ N`. So `Z_N ⊆ E_n ⊆ Z_(N−1)`.
  - Only `Z_N` or `Z_(N−1)` can equal it (Proposition C).
  - The two equalities are the negations of (ii) and (i), respectively.
- *Calibration.* Plausible. It cites `gq-bh-finf-hyp-pentagon-three-checks.md`, which is not reviewed.

**Theorem E: correct, with one repair.**
- *Finitely many types.*
  - Both fronts lie within `R(δ,|g|)` of `γ(n−|g|)`. For `E_n`, the ray from `g` at time `n` is within `2|g| + O(δ)`
    of `γ(n − |g|)`, via the Busemann shift.
  - A joint signature fixes one `ℓ` together with the cone types relative to `1` and relative to `g`. Then
    `prop:MakeMorphisms` in the `1`-tree, and in the `g`-tree applied to `g^(-1)E` with `g^(-1)ℓg`, gives both
    morphisms from the same `ℓ`.
  - This is "modulo BBMZ as stated", as the node says.
- *The type decides atomicity.* By Proposition C, `E_n` is an atom shadow iff it equals `Z_k(σ)` for some
  `k ∈ [n−|g|, n+|g|]`. Morphisms preserve relative depth.
- *The type decides the children.*
  - The children of `(Z, E)` are the pairs `(Z′, E′)` with `E′` a `g`-child of `E` and `Z′` the child of `Z`
    containing it.
  - Both morphisms are the same `ℓ` on shadows, so containment is preserved, and restriction gives morphisms of the
    children (`rem:SelfSimilarTree`).
- *Paths and points.* Nested atom shadows determine the horofunction on all of `G`, so each intersection is one
  point. Distinct paths separate.
- *So `sing(g)` is the set of paths visiting `T_sing` infinitely often.*
  - This is a `G_δ` subset of the compact path space, so the countable-or-continuum dichotomy also follows from the
    perfect-set property.
  - The graph argument: a path visiting `v` infinitely often stays in `SCC(v)` after its first visit.
- **Repair: the uncountability criterion as stated is wrong in a degenerate case.**
  - "Some type in `T_sing` lies in a strongly connected component that is not a single cycle" also counts
    **trivial** components: a single vertex without a loop, which a path visits at most once. It also ignores
    reachability.
  - **Correct form.** `sing(g)` is uncountable iff some type in `T_sing`, reachable from a level-`|g|` root type,
    lies in a **nontrivial** strongly connected component that is not a single simple cycle, counting parallel
    edges.
  - The same wording applies to Conjecture U's "branching component", in this node and in
    `q12-line-state-for-hyperbolic-hosts`.
- *Credit.* The analogy with Sidki's circuit dichotomy (polynomial versus exponential activity of finite-state
  automorphisms) is apt.

**Repairs in the same commit.** The edits to `countable-sets-never-separate-continua-without-local-cut-points` and
`q12-line-state-for-hyperbolic-hosts` match my review of 21a84b5e16: "with overwhelming probability", and
Conjecture U also needing frontier Theorem 1.

**Verdict.**
- Lemma B, Proposition C, Theorem D and Theorem E: PASS, with the criterion repaired.
- Theorem A: its changed step PASSes; the underlying cone-matching theorem was not re-reviewed.
