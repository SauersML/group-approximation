---
rg: 2
id: out-free-sphere-lamination-coordinates-give-a-pip-action
kind: claim
title: For n at least three, the closure of projectivized weighted sphere systems of the doubled handlebody M_n, in Hatcher normal coordinates relative to a maximal sphere system, is a compact rational polyhedron on which Out(F_n) acts faithfully by piecewise-integral-projective homeomorphisms
distinct_from:
  out-free-pip-actions-need-dimension-two-and-genuine-pieces: that rules out circles, graphs, single linear pieces and finite length coordinates; this proposes the one remaining natural candidate, coordinates by splittings (spheres) instead of conjugacy classes.
  out-free-acts-on-boundary-by-piecewise-representatives: that is the band route's missing lemma (PR); this would bypass the band entirely, as PML does for closed mapping class groups.
artifacts:
  - research/artifacts/gq-bh-outfn-2-sphere-normal-coordinates.md
---

**OPEN** (proposed by bh-outfn-2, 2026-09-18). Setting: `M_n = #^n S^1 × S^2`,
`π_1 = F_n`. Isotopy classes of essential sphere systems are the simplices of the free
splitting complex (Hatcher; recalled). `Out(F_n)` acts on them faithfully for `n ≥ 3`
(Aramayona–Souto, `Aut(FS_n) = Out(F_n)`; recalled). Fix a maximal sphere system `Σ` of
`3n − 3` spheres. It cuts `M_n` into `2n − 2` copies of `P = S^3` minus 3 balls.

**Claim.** Let `𝒩(Σ)` be the space of normal coordinates below, and `𝒮_n` the closure in
`P(𝒩(Σ))` of the projectivized weighted sphere systems in normal form. Then:
- (i) `𝒮_n` is a compact rational polyhedron, a finite union of projectivized rational cones;
- (ii) each `q ∈ Out(F_n)` acts on `𝒮_n` by a PIP homeomorphism;
- (iii) the action is faithful.

If so, `Out(F_n)` enters the closed-MCG host machinery (`board/major-mcg.md`, `𝒯_m` and the
edge-split operad), after replacing the sphere `S^m` by the rational polyhedron `𝒮_n`.

## Evidence (lane analysis, not proofs)

1. **Finitely many piece types.** Hatcher's normal form puts any sphere system `S` in a form
   where `S ∩ P` consists of pieces meeting each boundary sphere of `P` in at most one circle.
   Normal form is unique up to normal isotopy (recalled). The pieces are:
   - essential disks `D_i`, bounded on `∂_i` and separating the other two boundary spheres;
   - cylinders `C_ij`;
   - pants `P_123`.

   That makes 7 types. `D_i` is incompatible with `P_123` and with `C_jk`, since a connected
   piece joining `∂_j` to `∂_k` crosses it. So the admissible type sets form a finite
   complex, exactly as in normal surface theory.
2. **No twist parameters.** On each boundary sphere `∂_i` of `P`, every circle of every
   piece separates the directions of the other two boundary spheres. So the circles form one
   linear chain of parallel circles. Two chains of the same length on `S^2` are isotopic.
   Matching across a sphere of `Σ` therefore imposes one linear equation (equal circle
   counts) plus at most a finite orientation datum. This is the point where spheres are
   simpler than curves.
3. **Integral structure.** Normal coordinates of systems are integral. Weighted systems give
   the rational points, and changing `Σ` to `φ(Σ)` computes the action.

## Obstacles found (these decide the claim)

- **(O1) Dimension.** On the generic admissible cone the coordinates per piece are
  `(p, c_12, c_13, c_23)`. So `𝒩(Σ)` has dimension `4(2n−2) − (3n−3) = 5n − 5`. Each
  simplex of weighted sphere systems has dimension at most `3n − 3`, but infinitely many
  simplices can be dense in more, as multicurves (dimension `3g−3`) are dense in ML
  (dimension `6g−6`). The very small trees have dimension only `3n − 3`, so a
  `(5n−5)`-dimensional `𝒮_n` would map to them with positive-dimensional fibers.
  - The **sphere condition** is not linear. Gluing pieces gives closed surfaces of any genus
    (tori appear), and "all components are spheres" means that each component's piece graph
    is a tree.
  - So `𝒮_n` is the closure of a non-linear subset of integral points. (i) asks that this
    closure be polyhedral, for example all of `𝒩(Σ)` or a rational subfan. For curves on
    surfaces every admissible integral point is a multicurve. Here tori are admissible, so
    density is the question.
- **(O2) Coordinate change.** (ii) needs the effect of one elementary move on normal
  coordinates to be piecewise integral-linear with finitely many pieces. The move replaces
  one sphere of `Σ`, a Whitehead move of the dual trivalent graph. For curves this is the
  max-plus flip formula. For spheres no formula is known to this lane.
- **(O3) Rank two.** The inversion `x ↦ x^{-1}`, `y ↦ y^{-1}` fixes every free splitting of
  `F_2`, so the action is not faithful at `n = 2`. That is consistent with (iii) being
  claimed only for `n ≥ 3`.
- **(O4) Relation to `\bar{CV_n}`.** The dual-tree map `𝒮_n → \bar{CV_n}` is equivariant but
  not known to be injective or surjective. So (i)–(iii) are not implied by, and do not imply,
  any known property of the Culler–Vogtmann compactification.

## Suggested attack

Settle (O1) in rank 3.
- `Σ` has 6 spheres, and there are 4 pieces `P`. `𝒩(Σ)` has dimension 10, each simplex of sphere
  systems has dimension 6, and very small trees have dimension 6.
- Enumerate normal sphere systems up to a small circle count (a bounded, exact enumeration,
  suitable for one short MSI job).
- Test whether their projective closure is a rational subfan, and find its dimension (6, 10,
  or in between). A clean negative, a non-polyhedral closure, would close this route. A
  positive would be the first integral piecewise-linear model of `Out(F_3)`.

## Computation (2026-09-18, `research/artifacts/gq-bh-outfn-2-sphere-normal-coordinates.md`)

One Slurm job computed normal coordinates of 3000 spheres of `M_2` and 8001 of `M_3`. It used boundary cuts:
the crossed edges of `T_Σ` form a core subtree, and its vertex degrees give the piece types. All matching,
Euler and compatibility checks passed.
- **Rank 2 (calibration).** 15 support classes, stable from BFS depth 5, each spanning its whole matching
  cone. This is the finite piecewise-linear Farey structure.
- **Rank 3.**
  - Support classes do not close up by depth 9: 2, 7, 14, 30, 55, 98, 180, 333, 612, 990, growing about 1.7×
    per level.
  - One class spans 8 dimensions, affine span 7, against `3n − 3 = 6` for Outer space. This supports (O1):
    normal coordinates see more than trees.
  - The 25 largest classes each span their matching cone.
- Polyhedrality is **not decided**: zero patterns are finitely many a priori. The decisive next test is the
  density of spheres among admissible integral points inside one filled class, via the tree condition.
