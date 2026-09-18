---
rg: 2
id: a2-lattices-lie-in-permutational-bh-class
kind: claim
title: Every discrete cocompact group acting on a locally finite thick Ã₂ building lies in the permutational Boone–Higman class B_A, so finite direct products and finite-index overgroups of such lattices also embed in finitely presented simple groups
distinct_from:
  a2-lattices-satisfy-permutational-boone-higman: same theorem, landed by bh-lattices at b36cd68bd (10:20:14), 83 s before this node, through their general degree-category tool; this node is an independent derivation restricted to the phase-0 piece. Cite that node; this one is kept as a cross-check.
  a2-lattices-embed-in-fp-simple-groups: that embeds each lattice in a finitely presented simple group through Matui's simplicity theorem; this puts the same full groups into B_A through a type (A) action on clopen sets, which gives the stronger closure properties of B_A.
  stabilized-kgraph-full-groups-have-type-a-actions: that is the comparison argument for finite k-graphs without units; this runs it for the orbit category of an Ã₂ lattice, whose units are the finite tile stabilizers.
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

**ESTABLISHED** (duplicate of `a2-lattices-satisfy-permutational-boone-higman`, which has priority; both are subsumed by `euclidean-building-lattices-lie-in-permutational-bh-class`). Lane proof, bh-groupoid 2026-09-18, below; not independently reviewed; no
priority claimed). It combines `a2-lattices-embed-in-fp-simple-groups` (notation: `ℭ_Γ`,
`𝒢_Γ`, `𝒮_a`) with the comparison method of `stabilized-kgraph-full-group-clopen-action-proof`
by bh-lattices.

## Statement

Let `Γ` be a discrete cocompact group of automorphisms of a locally finite thick Ã₂ building.
Then `Γ ∈ B_A`. Hence, by `boone-higman-type-a-class-closed-under-finite-extensions`, every
group commensurable with a finite direct product of such lattices embeds in a finitely
presented simple group.

## Proof

**Reduction.** By closure of `B_A` under finite-index overgroups, we may assume `Γ` is type
rotating.

**Step 1: the stabilized category.**
- Rescale `ℭ_Γ` by `n = 3m` and restrict to one strongly connected piece. By Step 4 of the
  reference node, the pieces are the whole category if the type-rotation character `θ ≠ 0`,
  and the three phases if `θ = 0`. Choose `m` so that every object has at least two loops of
  each colour.
- Put `ℭ'' = ℭ_Γ^(n) × O_2`, with an `N³`-valued degree.
- Its Li groupoid is `𝒢'' = 𝒢_Γ^(n) × 𝒢_{O_2}`: arrows split coordinatewise (as in Step 5.2
  there).
- Let `C''` be the union of the object cylinders of the phase-0 piece, times `{0,1}^N`.
- `D = F(𝒢''|_{C''})` is of type `F_∞` by Li's `thm:deg`, exactly as in Step 5.3 of the
  reference node. Condition (F) holds by right cancellation, and the units `K_a` are finite.

**Step 2: comparison.** Any two nonempty clopen subsets of `C''` are exchanged by a compact
open bisection of `𝒢''`.
- **Cylinders.** A cylinder is `∂Ω(cℭ'')` for a morphism `c`. Prefix replacement
  identifies it with the object cylinder of its source, through a bisection.
- **Decompositions.** Every compact open set is a finite disjoint union of cylinders. By
  Li's basis, it is a finite Boolean combination of principal ideals, and constructible
  ideals are finite disjoint unions of principal ones (Step 1 of the reference). Refine to a
  common degree.
- **Equal type vectors.** Record the number of cylinders with each source object. If two
  decompositions have equal vectors, pair up the cylinders and glue the prefix replacements.
- **Refinement moves.** Take a colour `j` and a transversal `T_j(w)` of the degree-`ε_j`
  morphisms from `w` modulo units. By (UFP\*), and because boundary points are infinite
  chains, `∂Ω(cℭ'') = ⊔_{e ∈ T_j(w)} ∂Ω(ceℭ'')`.
  - In a `ℭ_Γ^(n)` colour, the source `w` survives (loops), and the other sources join the
    support.
  - In the `O_2` colour, the move adds exactly one cylinder with source `w`.
- **Conclusion.** The piece is strongly connected, so the moves make the support the whole
  piece and then equalize the counts. This is Step 3 of bh-lattices' route, with morphisms
  modulo units in place of paths.

**Step 3: type (A).** `D` acts on the countable set of nonempty proper clopen subsets of
`C''`, and this action is of type (A). The argument is Step 4 of bh-lattices' route
verbatim.
- **Faithful.** Clopen sets separate points.
- **Finitely many orbits on pairs.** A pair is determined by which of its four Boolean atoms
  are nonempty, and matching atoms are equivalent by Step 2.
- **Finitely generated stabilizers.** The stabilizer of `U` is `F(𝒢''|_U) × F(𝒢''|_{C''∖U})`.
  Each factor is conjugate by a bisection to `D`, which is finitely presented.

**Step 4: Γ ≤ D.**
- `Γ ↪ F(𝒢_Γ^D)`, the amplified groupoid on `⊔_{d∈D} 𝒮_{a(d)}` (Step 3 of the reference).
  All decorations `d` are tiles based at `O`, so they have phase 0.
- The skew-product and compression steps (Steps 2–3 of
  `primitive-two-graph-fp-simple-embedding-proof`, and their `L/nZ²` version in
  `type-preserving-vertex-free-a2-groups-embed-in-fp-simple-groups`) use only explicit
  bisections, built from morphisms of prescribed degree between objects of the phase-0 piece.
  With distinct morphisms `ρ` chosen for each `d ∈ D` as well, they embed `F(𝒢_Γ^D)` in
  `F(𝒢_Γ^(n)|_{C_0})`.
- Then `g ↦ g × id` embeds this in `D`.
- So `Γ ≤ D`, and `D` has a type (A) action. Hence `Γ ∈ B_A`. ∎

## Remarks

- **Consistency.** Step 4 does not use pure infiniteness or Matui comparison. This is
  consistent with bh-lattices' correction that Matui proves comparison only for shifts of
  finite type.
- **Free case.** The vertex-free case (`vertex-free-type-rotating-a2-groups-satisfy-boone-higman`)
  is the special case with trivial units. There `stabilized-kgraph-full-groups-have-type-a-actions`
  applies directly to the phase pieces of `Λ_Γ^(n)`.
