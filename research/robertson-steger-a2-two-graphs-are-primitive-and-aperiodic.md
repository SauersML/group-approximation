---
rg: 2
id: robertson-steger-a2-two-graphs-are-primitive-and-aperiodic
kind: claim
title: The Robertson–Steger 2-graph of a type rotating group acting freely on the vertices of an Ã₂ building with finitely many orbits is primitive in both colours and aperiodic
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
refuted_by:
  - rs-strip-tail-transitivity-forces-primitive-transition-matrices
---

**REFUTED as stated** (bh-groupoid, 2026-09-18). A type-preserving `Γ` never has primitive
`M_1`, `M_2`: the base type of a tile increases by one along each colour-1 edge and by two along
each colour-2 edge, so both graphs have period divisible by 3
(`rs-strip-tail-transitivity-forces-primitive-transition-matrices`, item 1). Every torsion-free
cocompact lattice in `SL_3(Q_p)` is a counterexample. See "Corrected form" below.

**Original statement (kept for the record).** Let `B` be a locally finite thick Ã₂ building and `Γ` a group of type rotating
automorphisms acting freely on the vertices of `B` with finitely many orbits. Let `M_1`,
`M_2` be the Robertson–Steger transition matrices on the alphabet `A = Γ \ 𝔗`, and `Λ_Γ`
the finite 2-graph they define. Claim: `M_1` and `M_2` are primitive, and `Λ_Γ` is
aperiodic in the Kumjian–Pask sense.

**What is known** (`robertson-steger-a2-boundary-algebras-are-rank-two-ck`):
- (H0), (H1) and (H3) hold for every such `Γ`. (H3) gives, for each nonzero `p`, a word
  that is not `p`-periodic.
- Each `M_i` has an irreducible graph when `B` is the building of `PGL_3(K)`,
  `K` a characteristic-zero local field and `Γ` a lattice. That argument uses Mozes' idea
  and the ergodic theory of `SL_3(K)`, so it does not reach exotic buildings.
- Irreducibility is weaker than primitivity (it allows periodicity).

**Why it matters.** Together with `a2-group-embeds-in-full-group-of-its-rs-two-graph` and
`primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple`, it would give
Boone–Higman for these groups. That includes the Cartwright–Mantero–Steger–Zappa groups
acting simply transitively on exotic Ã₂ buildings, which have no infinite linear images
(see `exotic-a2-lattices-satisfy-boone-higman` for the Bader–Caprace–Lécureux pin).

**Kill test / next step.** For one explicit CMSZ triangle presentation on an exotic
building, compute `M_1`, `M_2` from the tiles and check `M_i^k > 0` for some `k`, a
finite certificate. A geometric proof for all `Γ` would need minimality and a
mixing-type property of the boundary action of `Γ` on `Ω`.

## Corrected form and status (2026-09-18, bh-groupoid)

Let `θ: Γ -> Z/3` be the type-rotation character. The corrected claim:
- if `θ` is onto (for example, vertex-transitive groups such as the CMSZ groups), `M_1` and
  `M_2` are primitive;
- if `θ = 0`, they are irreducible of period 3.

What is known about it (all lane proofs, not reviewed):
- **Aperiodicity is automatic** once each `M_i` is irreducible, through (H3)
  (`rs-two-graph-aperiodicity-from-h3-and-irreducibility`, via Robertson–Sims'
  finite-path criterion read at source).
- **Linear case.** The corrected claim holds for lattices in `PGL_3(K)` with `K` of
  characteristic zero, through Robertson–Steger's Howe–Moore ergodicity
  (`rs-strip-tail-transitivity-forces-primitive-transition-matrices`, item 3).
- **Explicit instances.** Five CMSZ groups of order 2 and two of order 3 are certified
  primitive by computation (`cmsz-rs-two-graphs-of-orders-two-and-three-are-primitive`).
- **Exotic case.** Open. It reduces to ergodicity of `ker θ` on each typed space of tail
  classes of marked singular half-strips (item 2 of the same node).
  - Bader–Caprace–Lécureux's singular Cartan flow ergodicity (arXiv:1608.06265, Theorem
    `ergodic`) is phase-free.
  - It should give irreducibility of `M_1` and `M_2`, which is not written out.
  - Primitivity needs its phase-sensitive refinement.
