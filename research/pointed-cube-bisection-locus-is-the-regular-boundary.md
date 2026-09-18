---
rg: 2
id: pointed-cube-bisection-locus-is-the-regular-boundary
kind: claim
title: A cubulated group acts on its Roller boundary by germs of the pointed-cube groupoid exactly at the regular points; so a closed carrier exists only inside the regular boundary, and for Z^2 * Z none exists at all
requires:
  - cubulated-groups-act-by-bisections-of-a-pointed-cube-category
  - cuntz-stabilized-garside-full-groups-are-f-infinity
distinct_from:
  cubulated-groups-act-by-bisections-of-a-pointed-cube-category: that proves the bisection action at regular points and lists closedness of R as a gate; this proves the converse (no germ at any non-regular point) and shows the gate fails for a RAAG.
  cuntz-stabilized-garside-full-groups-are-f-infinity: that closes the finiteness gate; this shows the carrier gate G1 is the real obstruction for the pointed-cube route.
---

**ESTABLISHED** through `pointed-cube-bisection-locus-proof` (lane proof, elementary apart
from standard CAT(0) cube complex facts; not independently reviewed; no priority claimed).

## Setting

- `X` is a locally finite, finite-dimensional, **essential** CAT(0) cube complex.
- `G` acts on `X` freely on vertices and cocompactly.
- `C_X` is the pointed-cube category, with base vertex `o`.
- **Regular points.** `R ⊆ ∂_R X` is the set of points whose geodesic rays from `o` eventually
  leave the carrier of every hyperplane. This does not depend on the ray chosen.
- **(TF).** No nontrivial element of `G` fixes a nonempty open subset of `∂_R X` pointwise.
- A **germ** of `g` at `ω` means that near `ω`, `g` agrees with one prefix replacement
  `λw ↦ μw` of `I_l ⋉ Ω_∞`.

## Statement

1. **Identification.** The base cone of Li's `Ω_∞(C_X)` is the Roller boundary `∂_R X`, with
   its usual topology. The cylinder of `o → z` is `{ω : H(o,z) ⊆ H(o,ω)}`.
2. **Bisection locus.** Under (TF), every `g ∈ G` has a germ at `ω` if and only if `ω ∈ R`.
   - At a non-regular `ω`, the geodesic rays eventually run inside the carrier of some
     hyperplane `H`.
   - Any `g` whose hyperplane set `H(g^{-1}o, o)` contains `H` has no germ at `ω`.
3. **Carrier gate.** Let `Z ⊆ Ω_∞` be closed and invariant, and suppose `G` acts on
   `Z ∩ cone(o)` by global bisections. Then `Z ∩ cone(o) ⊆ R`. So gate (G1) of
   `virtually-torsion-free-cubulated-groups-satisfy-boone-higman` can hold only inside the
   regular boundary.
   - If `R` is closed, `Z` can be its saturation. This is the case for products of thick
     trees, and it is the route of item 3 bis there.
   - If `R` is not closed, `Z` must avoid every non-regular limit of regular points.
4. **The route fails for `Z² * Z`.** Take `X` the universal cover of the torus wedge a
   circle (squares from `[a,b]`, plus a loop `c`), with `G = Z² * Z`. This `X` is
   essential, (TF) holds, and:
   - the point `ω = (+∞, 0)` of the base flat is non-regular;
   - it is a limit of regular points that leave the flat through `c`-edges;
   - every nonempty closed invariant `Z ⊆ Ω_∞` contains `ω`.

   So **no** closed invariant set carries the `G`-action by bisections. The
   pointed-cube-plus-Cuntz route cannot reach even this RAAG (a special group, so the
   route was never needed for it). In general the route reaches exactly the cubulations
   that have a closed regular carrier.

## What this pins down for Q1.15

After `cuntz-stabilized-garside-full-groups-are-f-infinity` removed the finiteness gate, the
binding gate is **(G1)**, and it is geometric: the pointed-cube coding remembers which
adjacent hyperplanes were crossed from the base point. Along a tail that runs beside a
hyperplane, codings from `o` and from `go` never resynchronize. So each `g` acts there by
a finite-state transducer that never synchronizes (as in BBCMP's rational embedding), not
by a finite union of prefix replacements.

- (G2) holds whenever the carrier is regular.
- (G3) is only needed once (G1) holds.

A route to Q1.15 for cubulations that are not products of trees needs a **new coding**, one
that absorbs the persistent "which side was crossed first" flag carried along hyperplane
strata.

## Lesson for general BH

A finitely coded host sees a group element as a bisection only where codings from
different base points **resynchronize**. For geodesic codings of nonpositively curved
spaces, that happens exactly at points that eventually leave every wall's carrier.

So the invariant to compute for any geometric coding is its **resynchronization locus**,
and a closed carrier must lie inside it. Finiteness (now automatic after Cuntz
stabilization) and rank were never the obstruction for cubulated groups. Parallelism of
tails to walls is. The next host design must stratify the boundary by the walls a tail
runs along, since those strata are Roller boundaries of hyperplanes, one dimension down.
