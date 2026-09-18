---
rg: 2
id: euclidean-building-boundary-shifts-are-quantum-rigid
kind: claim
title: The chamber-boundary shift of a lattice in a thick Euclidean building, as a subshift over the lattice itself, is quantum rigid (the higher-rank analogue of free-group boundary shifts)
distinct_from:
  thick-building-flat-sfts-are-never-quantum-rigid: that codes the building over its translation lattice Z^d and is never rigid; this codes it over the lattice Γ acting on its own boundary, where no both-sided branching is visible.
  boundary-crossed-product-is-a-leavitt-path-algebra: that is the rank-one case (F_d on its Cayley tree), which is finitely presented; this asks for the rank-two and higher analogue and for quantum rigidity itself.
  euclidean-building-lattices-lie-in-permutational-bh-class: that is the one-sided (tail-equivalence) coding of the same boundary, which gives B_A for Γ; this is the two-sided group-shift coding Γ ↷ Ω, which gate G2 of the master route needs.
  free-minimal-z2-sft-is-quantum-rigid: that is the Z^2 calibration of gate G2; this is the one-ended, non-amenable, Kazhdan test case that building geometry can offer.
---

**OPEN.** Posed by bh-g2-buildings (2026-09-18) for gate G2 of
`research/artifacts/gq-bh-synthesis-master-route.md`. Nothing here is proved except where stated.

## Statement

- **Setting.** Let `Γ` act simply transitively on the vertices of a special type of a locally finite thick
  Euclidean building `Δ`, with base vertex `o`. Examples are the CMSZ `Ã₂` groups, which are finitely
  presented, one-ended, Kazhdan and non-amenable. Let `Ω` be the space of chambers at infinity.
- **The encoding.** For `c ∈ Ω` put `x_c(γ) = γ^(-1) · germ_(γo) Q(γo, c)`. This is the germ at `o` of
  the translated sector, an element of the finite set `𝒜` of chambers at `o`.
- **Equivariance.** `x_(gc)(h) = x_c(g^(-1)h)`, so `c ↦ x_c` is a `Γ`-equivariant homeomorphism onto a
  subshift `X_Ω ⊆ 𝒜^Γ`. It is injective because sector germs at all vertices determine `c`.
- **Claim.** `X_Ω` is `D`-quantum rigid over `F_2` (and over every field) for some `D`, in the sense of
  `fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## What is known

- **Rank one.** For `Γ = F_d` on its Cayley tree, `X_Ω` is the boundary shift.
  `LC(∂F_d, k) ⋊ F_d` is a Leavitt path algebra, hence finitely presented
  (`boundary-crossed-product-is-a-leavitt-path-algebra`, review PASS). Its difference sets are lines,
  noted in `fp-crossed-products-force-connected-differences`. Whether that group shift is quantum rigid
  in the Q1–Q3 sense has not been checked. The converse "finitely presented crossed product implies
  quantum rigid" is proved only over `Z^2` (`sft-crossed-product-fp-iff-quantum-rigid`).
- **Rank two, recalled.** Robertson–Steger identify `C(Ω) ⋊ Γ` with their rank-two Cuntz–Krieger
  algebra (Crelle 1999, not re-read). The algebraic version would make `LC(Ω, k) ⋊ Γ` a Kumjian–Pask
  algebra of a finite 2-graph, and such algebras are finitely presented; this is not checked. If it
  holds:
  - `fp-crossed-products-force-sft-over-any-group` makes `X_Ω` an SFT over `Γ`;
  - `fp-crossed-products-force-connected-differences` makes its difference sets coarsely connected.
- **Dynamics.** Minimality and topological freeness hold. bh-groupoid read these at source
  (Ciobotaru–Le Bars, arXiv:2601.13092).

## Why it matters, and its limits

- **The payoff.** A yes would give the first quantum-rigid minimal subshift over a one-ended,
  non-amenable, Kazhdan group. That is the object the synthesis calls the most informative, in the only
  form building geometry offers. The flat coding over `Z^d` is dead
  (`thick-building-flat-sfts-are-never-quantum-rigid`).
- **Not free.** `X_Ω` is only topologically free, not free. An element that stabilizes an apartment and
  translates it fixes that apartment's chambers at infinity. Cocompact lattices contain such elements
  via periodic flats (Ballmann–Brin for `d = 2`, recalled, not re-read). The master route's (★) asks
  for a free subshift. So this candidate helps only if one of these holds:
  - **Ring side.** The ring-side gates (K-theory of the Leavitt tensor, and simplicity) work for minimal
    topologically free actions. `free-action-leavitt-tensor-hosts-have-trivial-k1-k2` assumes freeness.
  - **Coupling.** It is coupled with a free factor, which reopens the coupling problem of design rule 2.
- **Coverage.** It codes only `Γ`. For a general input `G`, it can enter only as the coupled `H`-factor
  of `Λ = Λ_0 × H`.

## Suggested first steps

1. Check quantum rigidity of the rank-one boundary shift directly. The tool is a propagation argument
   along the unique geodesic from each vertex toward the end. If it fails there, the candidate is dead.
2. Write the algebraic Robertson–Steger isomorphism with a Kumjian–Pask algebra over any field, in the
   style of the rank-one node.
3. Test the obstruction side: difference sets of two chambers at infinity are thickened apartments or
   roots. Find whether some pair has a difference set with two far components.

## Lesson for general BH

- **The flat coding.** The same building gives a never-rigid translation coding. The branching across
  walls is independent on the two sides.
- **The one-sided coding.** It gives finitely presented full groups; the branching becomes compression.
- **The lattice coding.** The two-sided coding by the lattice itself is the only one still open. There
  the group, not a translation lattice, carries the geometry, so branching toward infinity is shared by
  all neighbours.
- **The general rule.** For group-shift rigidity, the acting group must be the object whose geometry
  the tiles encode. Tiling a quotient space by a translation lattice creates free directions.
