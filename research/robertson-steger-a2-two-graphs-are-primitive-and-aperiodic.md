---
rg: 2
id: robertson-steger-a2-two-graphs-are-primitive-and-aperiodic
kind: claim
title: The Robertson–Steger 2-graph of a type rotating group acting freely on the vertices of an Ã₂ building with finitely many orbits is primitive in both colours and aperiodic
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**OPEN.** Let `B` be a locally finite thick Ã₂ building and `Γ` a group of type rotating
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
