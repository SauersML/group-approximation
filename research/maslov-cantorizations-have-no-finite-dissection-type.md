---
rg: 2
id: maslov-cantorizations-have-no-finite-dissection-type
kind: claim
title: No Sp_4(Z)-invariant Maslov Cantorization of the Lagrangian Grassmannian has finite dissection type, so the Lagrangian Brin-Thompson group 2V_Λ(2) has no Sp_4(Z)-rigid pair-diagram calculus
distinct_from:
  unimodular-maslov-cells-do-not-dissect-mixed-atoms: that shows single cells are not enough; this shows that no finite family of region types is enough, whatever the regions.
  rational-projective-full-groups-are-finitely-presented: that is the sphere host, where one tile type (the unimodular simplex) dissects everything, because rational polyhedra have rational corners; this is the Lagrangian host, where corners fall over infinitely many quadratic fields.
  lagrangian-brin-thompson-group-is-finitely-presented: that is the open finiteness question; this excludes the standard method of answering it at n = 2, and does not decide it.
  deligne-lift-actions-are-not-almost-v: that excludes the Belk-Hyde-Matucci engine over V; this excludes the Stein-Farley pair-diagram engine with Sp_4(Z)-rigid pieces.
---

**ESTABLISHED.** Lane proof in `maslov-no-finite-dissection-type-proof`, not reviewed. No
priority is claimed.

## Setting

- `n = 2`, `Γ = Sp_4(Z)`, and `Λ = Λ_2(R)`. In the chart `S ∈ Sym_2(R)` of the standard
  frame, `Λ` is the conformal compactification of Minkowski space `R^{1,2}` (with
  `det S = t^2 − x^2 − y^2`). Maslov cycles `Σ(L)` are light cones.
- A **Maslov algebra** is a `Γ`-invariant Boolean algebra `𝔅` of regular open subsets of
  `Λ`, under the regular-open operations, such that:
  - it contains the algebra `𝔅_u` of `unimodular-maslov-cantorization-is-minimal-expansive`;
  - every member has boundary contained in a finite union of rational Maslov cycles.
  Examples: `𝔅_u` itself (the space `Y_u`), and the algebra of the Cantorization `Y_Λ` of
  `lagrangian-thompson-group-contains-deligne-lattice`.
- **Finite dissection type (FDT).** `𝔅` has FDT if there is a finite set `𝒯 ⊂ 𝔅 ∖ {∅}`
  such that every nonempty `B ∈ 𝔅` is a finite disjoint union of sets `γT`, with `γ ∈ Γ`
  and `T ∈ 𝒯`.
  - Disjoint union means pairwise disjoint pieces with `B = int cl(∪ pieces)`.

## Statement

1. **No FDT.** No Maslov algebra has finite dissection type.
2. **Diagrams force FDT.** Let `Y` be the Stone space of a Maslov algebra and `F` a finite
   `Γ`-set, and put `G = [[(Γ ⋉ (Y × F)) × G_2]]`. A **`Γ`-rigid pair-diagram calculus**
   for `G` is a finite family `𝒜` of clopen subsets of `Y × F` with the following
   property.
   - Every `g ∈ G` admits a finite partition of `Y × F × C` into rectangles `γA × C_w`,
     with `γ ∈ Γ` and `A ∈ 𝒜`.
   - On each rectangle, `g` acts by one element of `Γ` on the `Y × F` coordinate and by
     one map on the `C` coordinate.

   If such a calculus exists, `𝔅` has FDT.
3. **Consequence.** By items 1 and 2, `2V_Λ(2)` has no `Γ`-rigid pair-diagram calculus.
   This holds for `Y_u × (F_3^4 ∖ 0)`, for `Y_Λ`, and for every Maslov algebra.
   - The finite-presentation proofs for `V`, `nV`, `SV_G`, `𝒯_1` and `W` build a
     Stein–Farley or Brown complex out of diagrams. In those diagrams every piece is moved
     by a single element of the structure group.
   - For `2V_Λ(2)`, with structure group `Sp_4(Z)`, no such calculus exists. So those
     proofs do not transfer in their standard form.

## The mechanism: corner fields

- **Corners.** At a quadratic irrational point `q`, three rational light cones can meet
  transversally, and so cut out a pointed corner of some region of `𝔅_u`.
  - Any dissection must put a genuine corner of some tile at `q`.
  - The corners of finitely many tile types lie over finitely many number fields.
  - `Sp_4(Q)` preserves the field of definition of a point.
- **Fields.** For every odd prime `p`, the light cones of `0`, `I` and
  `R_p = diag(−1, 1/(p+1))` meet at the point
  `S_p = [[p, √(2p)], [√(2p), 2]] / (p+2)`,
  which is defined over `Q(√(2p))`.
- **Contrast.**
  - The regions of `𝒯_m` are rational polyhedral, and their corners are rational points.
    Every such region is a union of unimodular simplices (toric resolution), so FDT holds
    there with one type.
  - The cosets of `W` and the Farey arcs of `𝒯_1` are also finite type.

## Scope

- Proved for `n = 2`. For `n ≥ 3`, and for the full flag variety `G/B` of `Sp_4` (the
  other Deligne-admissible flag variety of
  `deligne-class-dies-over-flag-varieties-iff-flag-has-lagrangian`), the same corner
  argument is expected but not written.
- Not excluded:
  - diagram calculi whose rigid maps are not single elements of `Γ` on each piece, for
    instance after a non-algebraic `Γ`-equivariant recoordinatization of `Λ` (a
    "Lagrangian question-mark function");
  - finiteness proofs not based on diagrams.
- Finite presentation of `2V_Λ(2)` is not decided.

## Lesson for general BH

- **The engine needs rational corners.** The pair-diagram (Stein–Farley) engine requires
  finite dissection type. FDT forces the corner points of the Cantorization's regions
  into finitely many number fields. Walls that are hyperplanes (projective spaces, `𝒯_m`)
  or cosets (profinite spaces, `W`) meet at rational points.
- **Non-linear flag varieties.** The Schubert walls of a non-linear flag variety meet
  over infinitely many fields. This is proved here for `Λ_2`, and is expected whenever the
  flag variety is not a projective space.
- **Deligne's lattice.** By `deligne-class-dies-over-flag-varieties-iff-flag-has-lagrangian`,
  Deligne's lattice needs a Siegel-type flag variety. So among algebraic flag hosts, those
  admitting diagrams and those admitting Deligne's lattice are disjoint at `n = 2`.
- **What is left.** Deligne BH through full groups needs one of the following:
  - a non-algebraic Cantor model of `Λ` whose regions have rational corners;
  - a genuinely piecewise-linear `Sp_{2n}(Z)`-action on a sphere Cantorization that kills
    the class (`deligne-class-dies-on-some-rational-projective-host`), where FDT is
    automatic;
  - a finiteness theorem that does not use diagrams.
