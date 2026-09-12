---
rg: 2
id: strong-atiyah-kazhdan-edge-amalgam-permanence
kind: claim
title: Strong Atiyah passes to amalgams of torsion-free groups over an infinite property (T) edge
distinct_from:
  atiyah-kazhdan-edge-blocks-both-permanence-routes: that records why two known proof frameworks fail at a (T) edge; this is the permanence statement itself, which neither framework decides.
  atiyah-amalgam-unmixed-matrices-reduce-to-factors: that proves integrality for matrices supported in one vertex or the edge; this asks for integrality of every matrix over the amalgam.
  atiyah-passes-to-torsion-free-elementary-amenable-extensions: that is permanence under torsion-free elementary amenable quotients; this is permanence under amalgamation over a nonamenable Kazhdan edge.
  algebraic-strong-atiyah-counterexample-exists: that asks for any torsion-free counterexample; this is the specific permanence whose failure would give one on the compression-host amalgams.
artifacts:
  - research/artifacts/atiyah-vertex-mixing-2026-09-12.md
---

**OPEN.** Let `A` and `B` be torsion-free groups with a common infinite property (T) subgroup
`C`, and let `K <= C` be closed under complex conjugation. If `A`, `B` and `C` satisfy the Strong
Atiyah conjecture over `K`, then so does `G = A *_C B`.

This is the open host question for the Fournier–Facio double-HNN kernel amalgams
`P^(u_1) *_P P^(u_2)` over the Kazhdan subgroup `P`
(`fournier-facio-one-compressor-subgroup-reduces-to-gamma`). A failure would give a torsion-free
counterexample, and a proof would remove this host.

## Attempts

- **Amenable-edge flatness and Hughes-free division rings.** Both frameworks are dead at a (T)
  edge ([[atiyah-kazhdan-edge-blocks-both-permanence-routes]]).
- **Single-factor matrices.** Integral by induction
  ([[atiyah-amalgam-unmixed-matrices-reduce-to-factors]]). Any counterexample mixes both vertices.
- **Coproduct reduction.** [[atiyah-amalgam-rank-from-cohn-coproduct]] reduces the claim to
  integrality of one rank function on `D_A *_(D_C) D_B`. The uniform sufficient target is
  [[kazhdan-edge-coproduct-rank-is-inner-rank]], through the route
  `kazhdan-edge-amalgam-atiyah-via-coproduct-inner-rank`.
- **Property (T) through `L^2`-homology and approximation.** Neither applies: see the Attempts on
  [[kazhdan-edge-coproduct-rank-is-inner-rank]].
