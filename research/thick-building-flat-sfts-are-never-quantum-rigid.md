---
rg: 2
id: thick-building-flat-sfts-are-never-quantum-rigid
kind: claim
title: The apartment (flat) subshift of a torsion-free lattice in a thick Euclidean building, Mozes-type product-of-trees tilings included, branches across every wall, so it is never quantum rigid and its crossed product is never finitely presented
distinct_from:
  positive-entropy-sft-crossed-products-are-not-fp: that builds wall certificates from positive entropy; this builds them from thickness, and the flat subshifts of dimension at least 2 have zero entropy.
  antipodal-one-sided-group-shift-configurations-are-walls: that is for algebraic group shifts; this is for the geometric flat subshifts of buildings, where the two sides of a wall are independent half-apartments.
  a2-lattices-embed-in-fp-simple-groups: that uses link (pencil) closure to prove irreducibility of a one-sided sector coding; this shows the two-sided translation coding of the same buildings is never rigid, so link closure propagates reachability, not uniqueness.
  euclidean-building-lattices-lie-in-permutational-bh-class: that codes the building one-sidedly (sectors, tail equivalence, Li degree categories), where branching is compression; this is the two-sided translation coding, where the same branching is an independent fault.
  fp-crossed-products-force-connected-differences: that is the general wall obstruction over any group; this supplies the building instances of it, at every scale.
  v-times-golden-silver-wang-product-full-group-is-not-fp: that is the product-of-Wang-shifts warning; this is the building warning. Both are minimal-or-zero-entropy codings with independent far faults.
---

**ESTABLISHED (lane proof, bh-g2-buildings, 2026-09-18; not reviewed; no priority claimed).** It uses
standard building facts that were recalled, not re-read; they are listed in the route.

## Setting

- `Δ` is a locally finite thick Euclidean building of dimension `d >= 1`, with its complete apartment
  system. Any type is allowed, reducible or not. Examples:
  - products of thick trees, whose `d = 2` quotients are the VH-square complexes behind Mozes-type tilings;
  - `Ã₂`, `C̃₂` and `G̃₂` buildings, exotic ones included.
- `Γ ≤ Aut(Δ)` is type-preserving, cocompact and torsion-free, so simplex stabilizers are trivial.
- `Σ` is the model Coxeter complex, a chamber tiling of `R^d`. `L ≅ Z^d` is its translation lattice,
  `F` is a finite fundamental domain of chambers, and `p : Δ -> Γ\Δ` is the quotient.
- A **chart** is a type-preserving isomorphism `φ : Σ -> A` onto an apartment. It defines
  `x_φ ∈ 𝒜^L` by `x_φ(n) = (p∘φ)|_(n+F)`, where the finite alphabet `𝒜` consists of the type-preserving
  maps `F -> chambers(Γ\Δ)`.
- The **flat subshift** `X_Γ ⊆ 𝒜^L` is the set of all `x_φ`. It is closed and `L`-invariant. Local
  link rules, that the star of every vertex goes to an apartment of a link, cut it out as an SFT. That uses
  local-to-global for apartments (CAT(0) plus "full flats are apartments", recalled). Nothing below needs
  the SFT description.

## Theorem

For every `R` there are `x, y ∈ X_Γ` and parallel walls `H, H'` of `Σ` at distance `>= R` such that:
- `x(n) = y(n)` whenever `n + F` lies in the slab `S` between `H` and `H'`;
- `x` and `y` differ at some `n` on the far side of `H'`, and at some `n'` on the far side of `H`.

Hence, for every field `k`:
1. **Never quantum rigid.** `X_Γ` is not `D`-quantum rigid for any `D`: the wall certificate of
   `sft-crossed-product-fp-iff-quantum-rigid`, whose argument works over every `Z^d` and needs no
   mixing of configurations.
2. **Never finitely presented.** `LC(X_Γ, k) ⋊ Z^d` is not finitely presented, because
   `Δ(x, y)` is not `m`-connected for any `m` (`fp-crossed-products-force-connected-differences`).
3. **Subshifts.** The same holds for every subshift `Y ⊆ X_Γ` that contains such a pair for every `R`.
   If `Y` is also free, then no finitely presented subgroup of `F(G_V × (Z^d ⋉ Y))` contains the
   translations and site 3-cycles, by `fp-v-times-subshift-full-groups-force-quantum-rigidity`.
   In particular `A(G_V × (Z^d ⋉ Y))` is not finitely presented.

**The mechanism in one line.** Thickness means every root (half-apartment) lies in at least two
apartments. Replacing the part of an apartment above `H'` changes nothing below it, and replacing the
part below `H` changes nothing above. The two changes are independent far faults.

## Calibration

- **`d = 1`.** `X_Γ` is the positive-entropy Z-SFT of non-backtracking bi-infinite paths in the finite
  graph `Γ\T`, and it branches at every vertex.
- **`d = 2`, `T_1 × T_2` (Mozes-type).** A pattern on an `N × N` box is a pair of geodesic segments of
  length `N` modulo `Γ`, so there are at most `C (q_1 q_2)^N` of them and the entropy is zero. The
  subshift is still never rigid. So zero entropy is far from enough, as golden–silver already showed.
- **One-sided coding of the same buildings.** It is finitely presented. Its host full groups are
  finitely presented, and they are type (A) by bh-groupoid and bh-lattices. In a one-sided sector
  coding, branching at a wall is forward branching. Tail equivalence turns it into Higman–Thompson
  compression.
- **Mozes' own aperiodic tile sets.** They are decorated sub-SFTs, and were not read at source. The
  theorem applies to them exactly when their decorations leave both-sided branching for arbitrarily
  thick slabs. That is not checked here.

## Lesson for general BH

- **Thickness kills two-sided rigidity.** In a building, thickness is branching across
  codimension-one walls. Branching on both sides of a thick wall is exactly the independent far
  perturbation that the local rigidity principle forbids. So no two-sided translation coding whose
  local rules are "locally a thick building" is ever rigid.
- **Building arguments propagate reachability.** They prove irreducibility (pencil closure) and
  complete reducibility (counting). They do not prove uniqueness, so they cannot supply gate G2.
- **The same branching succeeds one-sidedly.** In the one-sided coding it is the compression that
  Li's theorem turns into finite presentation.
- **What a building-derived rigid SFT needs.** Decorations that determine the continuation across
  every wall on at least one side from the slab alone, as permutive and algebraic shifts do. The
  building's branching has to be killed, not used.
- **The live building candidate.** It is the coding by the lattice itself, not by the translation
  lattice (`euclidean-building-boundary-shifts-are-quantum-rigid`).

Route: `thick-building-flat-sfts-never-quantum-rigid-proof`.
