---
rg: 2
id: labbe-full-group-finite-small-growth-models-are-trivial
kind: claim
title: Finite models of Labbé's derived full group that satisfy all short relators and have quadratic Schreier growth carry the trivial action
distinct_from:
  aperiodic-sft-gated-models-break-refinement-relations: That kills gated rule actions on periodic colourings for ChJN's generators; this kills every finite model of quadratic growth, for any generating set, with no colouring or rule structure assumed.
  sfts-without-finite-orbits-are-not-residually-finite-actions: That excludes finite models close to the true action on the shift; this excludes finite models satisfying the group's short relators exactly, however far they are from the shift.
artifacts:
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

**ESTABLISHED** (reviewed 2026-09-13 by `ex-verify2-groups`: PASS, `research/artifacts/ex-review2-groups-2026-09-13-part9.md` §2).

**Setting.**
- `Gamma = D([[Z^2 ~ Omega_U]])` with a finite symmetric generating set `S`.
- An `F(S)`-set `O` is **`n`-exact** if every word of length `<= 2n` that is trivial in `Gamma` fixes every
  vertex of every Schreier ball `B_n(v)`.

**Statement.** For every `C` there is `n_0 = n_0(S, C)` such that every finite `n`-exact `F(S)`-set with
`n >= n_0` and `|B_k(v)| <= C k^2` (for all `v` and all `k <= n`) carries the trivial action.

**Two steps.**
1. **Corollary B (compactness).** Limits of such models are `Gamma`-sets of quadratic growth. By
   `labbe-full-group-small-growth-actions-are-standard` their orbits are fixed points or standard orbits. So
   for `n >= n_0` every `r_*`-ball of the model is trivial or orbital.
2. **Theorem C (charts).**
   - On a finite `F(S)`-set whose `r_*`-balls are all trivial or orbital, Schreier balls determine legal
     patches.
   - The 3-cycles `s(pi, ±e_i)` define commuting moves, and these give a `Z^2`-action with a legal Wang
     colouring.
   - Aperiodicity then leaves no moving vertex.
   - This completes Proposition L5 of `research/artifacts/labbe-lef-2026-09-12.md`, which was only sketched
     there.

**Consequences.**
- `labbe-relator-shift-periodic-points-carry-trivial-actions`: the relator-shift crux is false.
- A LEF witness for `Gamma` needs finite groups `G_n`, exact on `B_n(Gamma)`, all of whose quadratic-growth
  actions are trivial up to scale `n`. This is the non-spatial crux (C2). LEF itself stays open.

**Proof:** `labbe-full-group-finite-small-growth-models-are-trivial-proof`.
