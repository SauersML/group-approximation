---
rg: 2
id: nonamenable-products-have-minimal-sft-extensions-of-free-inputs
kind: claim
title: Over a product of two finitely generated non-amenable groups with decidable word problem, every effectively closed minimal free subshift is a factor of a minimal subshift of finite type
distinct_from:
  effective-minimal-subshifts-lift-to-plane-constant-minimal-sfts: that is the Z^2 simulation premise (M1), with a plane-constant factor and a hierarchy; this is the non-amenable-product analogue, with no plane structure, i.e. the minimal case of Barbieri–Sablik–Salo self-simulation.
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is the existence statement (P1); this is a simulation premise which, with (M2), gives P1 through minimal-free-sft-via-minimal-self-simulation-of-squares.
  plane-coupled-floating-tuples-are-jointly-diversifiable: that is the crux of the Z^2 design; this premise has its own form of the same crux, a phase field on unanchored grids, recorded below.
artifacts:
  - research/artifacts/gq-bh-bh-g1-simulation.md
---

**OPEN.** This is a restricted form of a printed question. Barbieri–Sablik–Salo,
arXiv:2104.05141 (TeX read at source), Section "Perspectives and questions", Question
`Q:minimal`, asks the following for every self-simulable group: does every minimal
(respectively transitive) effectively closed action have a minimal (respectively
transitive) SFT extension? By their Theorem `thm:selfsimulation`, every product of two
finitely generated non-amenable groups is self-simulable. This node restricts their
question to such products and to *free expansive* inputs. That is all the Boone–Higman
route needs.

**Statement.** Let `Γ_1, Γ_2` be finitely generated non-amenable groups such that
`Λ = Γ_1 x Γ_2` has decidable word problem. Let `Y ⊆ B^Λ` be nonempty, effectively
closed, minimal, and free. Then there are a nonempty minimal `Λ`-SFT `Z` and a factor
map `Z -> Y`.

Any such `Z` is free, since the stabilizer of a point is contained in the stabilizer of
its image.

## Known, read at source

**The non-minimal case is BSS Theorem `thm:selfsimulation`.** Its construction:
- **Paradoxical subshift.** On each factor, bounded 2-to-1 maps give disjoint one-sided
  paths, one indexed by each group element (Proposition `prop_ceccSilb`, Lemma
  `lem:injectivepaths`).
- **Grids.** Their product gives disjoint `N^2`-grids, again indexed by the group
  elements.
- **Computation.** Seeded Wang tilings run a machine that checks the set representation
  of the input on each grid.
- **Coherence.** Coherence rules compare each cell with its `|S|` neighbouring grids.
- There is no hierarchy.

**Obstacles BSS name for the minimal case.**
- **(a) Bi-infinite paths.** They are unavoidable in any paradoxical subshift, by
  compactness, and their computation layer is unrestricted.
- **(b) Return times.** Return times of the input and of the geometry layer can
  synchronize, creating patterns without bounded gaps.

**Also stated by BSS, without proof.** A minimal paradoxical SFT exists on `F_2`
(their tile set `M`).

**Amenable factors are outside the route.** `F_k x Z` is not self-simulable
(Proposition `prop:villexample`), so amenable second factors such as `Z` or `Z^2` are
excluded here. That is why the `Z^2` route needs a hierarchy.

## Design constraints (lane analysis by bh-g1-simulation; see artifact)

1. **The geometry must vary along both factors.** Suppose the grids were built only in a
   transverse factor `H`, constant along a factor carrying a non-SFT part of `Y`, with
   every cell reached at finite depth. Then each point is determined by its
   `Y`-coordinate together with a transverse invariant factor.
   - This is the situation of `injective-plane-lift-codings-force-finite-type`. Its
     proof is written for `H = Z^2`, but the steps use only that `H` is countable (a
     sketch, not re-proved here).
   - So minimality would force that part of `Y` to be of finite type.
   - Hence minimal self-simulation needs a minimal paradoxical geometry on each factor.
2. **Paradoxical geometry has no finite orbits.** A configuration invariant under a
   finite-index normal subgroup `N` would give a bounded 2-to-1 map that descends to a
   2-to-1 self-map of the finite set `N\Γ`, which is impossible. So the geometry layer
   is an infinite minimal SFT with no invariant probability measure.
3. **Hierarchy in place of seeds (proposal).** Let each grid carry a Durand–Romashchenko
   fixed-point tiling, with the input letters constant along one grid direction, instead
   of a seeded computation.
   - Such tilings are valid on `N^2`, `Z x N` and `Z^2` alike, and every local pattern
     lies in a finite macro-tile. So obstacle (a) no longer produces junk.
   - On an anchored grid (a quarter plane starting at a path origin) the hierarchy can be
     aligned with the corner. Its phase is then determined.
   - Phases float only on unanchored grids.
4. **What remains is obstacle (b), as a phase field on unanchored grids.** Local rules
   can relate the phases of neighbouring grids only by a closed relation `R_s`. There
   are three cases. This trichotomy is a heuristic sketch: (iii) follows from the lemma
   cited there, while (i) and (ii) assume the configurations described actually occur.
   - **(i) No relation.** Synchronized configurations exist, and patterns with unequal
     adjacent phases do not recur near them. So `Z` is not minimal.
   - **(ii) Equality.** The common phase of the unanchored grids near a point is
     preserved by the action, so it gives a continuous invariant function on the
     closure of those configurations. Minimality then leaves a single phase, and a
     phase that varies continuously cannot be single.
   - **(iii) Graphs of odometer translations.** The increments form a homomorphism
     `Λ -> odometer`. It is trivial on any minimally almost periodic subgroup
     (`simple-subgroups-act-trivially-on-equicontinuous-factors`), so the phases are
     constant along the cosets of the input.
   - So the phase field needs a genuinely relational coupling whose solution space is
     itself minimal. This is the non-amenable-product form of the joint-diversification
     crux `plane-coupled-floating-tuples-are-jointly-diversifiable`.

## Lesson for general BH

Both G1 routes have the same core.
- **On `Λ_0 x Z^2`,** the floating locus is the family of `Y`-data on infinite
  father-chains, indexed by planes.
- **On `Γ_1 x Γ_2`,** the non-amenable geometry removes the need for a hierarchy to
  *build* grids. The floating locus shrinks to the hierarchy phases of unanchored grids.

The missing object in both cases is a minimal, locally coupled field of hierarchy phases
over a group containing the input. It must be coupled relationally, since functional
couplings are excluded by the lemma above. The existence part of G1 (P1) is reduced to
building such a field, together with (M2).
