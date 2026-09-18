---
rg: 2
id: minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures
kind: claim
title: For every n and every subgroup K of nV with property (T), every minimal closed K-invariant subset of the Cantor cube carries a K-invariant probability measure
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that is finiteness of Kazhdan subgroups of nV; by kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures the two statements are equivalent, but this one is a statement about invariant measures of the action on the cube and can be attacked with paradoxicality and type-semigroup tools that say nothing about finiteness directly.
  heisenberg-in-nv-forces-drift-free-central-element: that assumes invariant measures and derives drift conditions for amenable subgroups; this asks for existence of invariant measures on minimal sets of Kazhdan subgroups.
  elek-free-minimal-cantor-actions-with-invariant-measures: that constructs some measured minimal Cantor action for every countable group; this asks that every minimal set of the given action of a Kazhdan subgroup of nV is measured.
artifacts:
  - research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md
  - research/artifacts/kazhdan-nv-slope-distortion-and-tail-gate-2026-09-17.md
---

Let `C = {0,1}^ω`, `n >= 1`, and `K <= nV` with property (T). Then every minimal
closed `K`-invariant subset of `C^n` carries a `K`-invariant Borel probability measure.

## Status

OPEN. Equivalent to `kazhdan-subgroups-of-brin-thompson-groups-are-finite` through
`kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures`:
- if Kazhdan subgroups of nV are finite, average the point masses of a finite orbit;
- conversely the route `kazhdan-nv-finite-via-measured-minimal-sets` gives
  finiteness from this claim.
So `n = 1` holds, through `thompson-v-has-haagerup-property`.

## What a counterexample must look like

An infinite Kazhdan `K <= nV` has the nonempty closed invariant set
`Z_K = C^n \ U_K` with no invariant probability measure, where `U_K` is the open set of
points having a clopen neighbourhood fixed pointwise by a finite-index subgroup. Every
invariant probability measure of `K` is carried by `U_K`.

## Constraints on a proof

- **It must use nV.** Abstract Kazhdan groups have measure-free minimal Cantor
  actions (for example `SL_3(Z[1/p])` on `P^2(Q_p)`, dense in the transitive action of
  `SL_3(Q_p)`, which preserves no probability measure by Furstenberg's lemma).
  Standard facts, not re-read at source.
- **It must use (T).** Ping-pong free subgroups of V have measure-free minimal sets.
- **Candidate tool.** For minimal ample actions, absence of an invariant probability
  measure is equivalent to a clopen paradoxical decomposition in the type semigroup
  (compare `algebraic-tarski-for-steinberg-algebras`). A proof could show that a clopen
  paradox on `Z_K` built from finitely many elements of `K` with slope data contradicts
  the spectral gap on `l^2` of marked pieces. This lane has not checked whether
  the type-semigroup equivalence applies to non-free minimal subsets like `Z_K`.

## Attempts

- 2026-09-17 (lane swarm-0917-w2-zar-pull-2, entropy-measure): reduced the finiteness
  hole to this claim; no progress on the claim itself. The shape-weighted brick
  families and the twisted Koopman representation of the Lebesgue measure both fail to
  give almost invariant vectors without an invariant measure (artifact Section 6).
- 2026-09-17 (lane swarm-0917 e-nv-kazhdan, minimal-counterexample): a biography of an
  infinite Kazhdan `K <= nV` and a split of this claim into two halves.
  - **Established.** `nv-point-germ-groups-embed-in-zn-by-slope`.
    - At a fixed point the slope decides the germ, so point germ groups of any
      subsystem are abelian of rank at most `n`.
    - This names the nV input the Constraints section asks for: `SL_3(Z[1/p])` on
      `P^2(Q_p)` has the non-abelian germ group `SL_2(Z[1/p])` at `[1:0:0]`, so it is
      not an nV subsystem.
    - A canonical brick self-compression meeting a closed invariant set forces a
      fixed point in that set with slope `-|u| ≠ 0`.
    - Stabilizers with property (T) are locally trivial. So finite orbits of `K`
      are slope-principal.
  - **Biography of a minimal `Z ⊆ Z_K`.**
    - `Z` is infinite and perfect, with no invariant measure.
    - Every orbit in `Z` has unbounded slopes. With bounded slopes, bricks of shape
      `c·1 + F(y)` are transported canonically along the orbit, giving a finite
      orbit of marked pieces and putting the point in `U_K`.
    - Point germs lie in `Z^n`.
    - Either `Z` is slope-principal, or some `g ∈ K` has a compressing fixed point
      (constant-sign slope) or a saddle (mixed signs, `n >= 2` only) in `Z`.
  - **Split, both halves OPEN.**
    - `minimal-sets-of-kazhdan-subgroups-of-nv-are-slope-principal`: all of (T) goes
      here. It is implied by finiteness.
    - `slope-principal-minimal-sets-of-nv-subgroups-carry-measures`: no (T), so it can
      fail on its own.
    - Route: `kazhdan-nv-measured-minimal-sets-via-slope-principality`.
  - **Where the direct argument dies.** Suppose the orbit height `F` is bounded
    below.
    - The bricks `B_y` of shape `c·1 + F(y)` are then canonically transported and
      level sets are finite.
    - A nested pair `B_y ⊊ B_x` gives a compression, hence a nonzero-slope fixed point
      in `Z`. For `n = 1` with a principal `Z` this is a contradiction once a nested
      pair exists.
    - But infinitely many bricks of increasing shape can form an antichain (`[1], [01], [001], …`),
      and for `n >= 2` Dickson's lemma orders shapes but not positions. Heights
      unbounded below break the canonical transport. The argument does not close.
  - **Class killed.** Any proof whose only nV-specific input is the shape of point germ
    groups (abelian of rank at most `n`), together with (T), minimality and
    measure-freeness, fails.
    - Torsion-free cocompact lattices in `Sp(k,1)`, `k >= 2`, have (T) and act on a
      minimal subset of the horofunction boundary of a Cayley graph. That subset is a
      totally disconnected infinite compact set mapping onto the Gromov boundary.
    - Its point stabilizers are cyclic and it has no invariant measure.
    - The imports are Kazhdan for `Sp(k,1)` and the map from the horofunction boundary
      onto the Gromov boundary. Both are standard and were not re-read at source.
    - Such a proof must use the slope values themselves, as the principal/compressing/saddle
      trichotomy does.
  - **Construction recipe.** For a counterexample, realize such a Cantor model inside
    `C^n` with generators acting by finite prefix replacement. Loxodromic fixed points
    must then carry nonzero slopes, compressing or saddle.
    - First finite step: take the rational (transducer) boundary action of a
      hyperbolic group from Belk–Bleak–Matucci, calibrating on a surface group, and
      test whether its states can be made trivial on deep cones after recoding
      coordinates into `n` binary streams.
    - Nontrivial tail states are the obstruction to lying in `nV`.
- 2026-09-17 (lane swarm-0917-w6-w6-re-pull-z-2, group-rings / transplanter). Three
  routes, none closing the claim; details in
  `research/artifacts/kazhdan-nv-slope-distortion-and-tail-gate-2026-09-17.md`.
  - Distortion route. Proved: `|s(w,x)|_1 <= B|w|_S`. So a nonzero slope at a periodic
    point makes the element undistorted, and a distorted element has `o(k)` slope
    growth. Dies at the passage to bounded slope at one point of a minimal set (the
    hypothesis of the Gottschalk–Hedlund node of lane c-kaznv). Bounded generation in
    `SL_3(Z)` needs exponents up to `exp(cL)`, so the bound stays linear. The route
    gives nothing for Kazhdan groups with undistorted cyclic subgroups (e.g. uniform
    `Sp(m,1)` lattices).
  - Product-tail gate. Proved: the orbit relation of `K` lies in `E_t^{×n}`, and each
    slope coordinate is the lag of that coordinate alone. The rank-two Robertson–Steger
    system has the same items without the per-coordinate witness. OPEN gate question:
    does `Γ ↷ Ω` admit continuous injective `(π_1, π_2) : Ω -> C²` whose coordinates
    witness the shape offsets as tail lags? "No" makes the product-factorization class
    kill formal. "Yes" is a step toward a counterexample.
  - Autonomous-coordinate induction. Duplicates the fibration-stabilizer node of lane
    c-kaznv. It dies at the first projection once coordinates are coupled (for example
    by a controlled flip).
