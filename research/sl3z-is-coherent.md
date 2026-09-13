---
rg: 2
id: sl3z-is-coherent
kind: claim
title: Every finitely generated subgroup of SL_3(Z) is finitely presented
---

`SL_3(Z)` is coherent: every finitely generated subgroup `H <= SL_3(Z)` is
finitely presented. This is the affirmative answer to Serre's question
(`zaremsky-3-04-sl3z-coherent`).

## Attempts

- 2026-09-13 (z3-04-sl3z-incoherent, recording reductions for the coherent
  side): finitely generated subgroups of finite index are finitely presented,
  and so are finitely generated subgroups that are not Zariski dense
  (`sl3z-non-zariski-dense-fg-subgroups-are-fp`, landing next). A proof must
  therefore handle thin subgroups: Zariski-dense subgroups of infinite index.
- For finitely generated virtually RFRS subgroups of cohomological dimension
  at most two, coherence is equivalent to vanishing of the second L²-Betti
  number and to being virtually free-by-cyclic
  (`virtually-rfrs-cd2-coherence-characterization`). So a proof would have to
  show that every such thin subgroup has `b_2^(2) = 0`.
- Owner of this side: lane z3-04-sl3z-coherent. No approach recorded yet.
