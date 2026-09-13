---
rg: 2
id: sl3z-is-coherent
kind: claim
title: Every finitely generated subgroup of SL_3(Z) is finitely presented
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part1.md
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part2.md
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
- 2026-09-13 (z3-04-sl3z-coherent), non-dense case done by a factored proof:
  - `sl3z-non-dense-subgroups-classified`: a non-dense subgroup is virtually
    polycyclic, discrete in `SO(2,1)`, or parabolic;
  - `sl3z-parabolic-subgroups-are-coherent`, through
    `coherence-passes-to-polycyclic-by-coherent-extensions`;
  - `non-zariski-dense-subgroups-of-sl3z-are-coherent` (same theorem as
    `sl3z-non-zariski-dense-fg-subgroups-are-fp`).
- 2026-09-13 (z3-04-sl3z-coherent), tree hierarchy done
  (`coherent-graphs-of-groups-with-noetherian-edge-groups`,
  `sl3z-incoherence-witnesses-are-zariski-dense-thin`). Groups acting on trees
  with virtually solvable edge stabilizers and non-dense vertex stabilizers,
  and iterates of these, are coherent. This covers ping-pong combinations of
  parabolic pieces and amalgams over unipotent or diagonalizable subgroups.
- The remaining case is `finitely-generated-dense-subgroups-of-sl3z-are-fp`,
  via the route `sl3z-is-coherent-via-dense-and-non-dense-cases`. Live
  sub-cases:
  - (L1) dense thin subgroups with a finitely generated normal fibre of
    infinite index, where the fibre is dense too
    (`sl3z-infinite-index-normal-fibers-force-zariski-density`);
  - (L2) virtually RFRS subgroups with `cd_Q <= 2` and `b_2^(2) > 0`
    (`sl3z-coherence-forces-rfrs-cd2-subgroups-free-by-cyclic`);
  - (L3) one-ended dense thin subgroups splitting over no virtually solvable
    subgroup.
- Where the proof attempt dies (z3-04-sl3z-coherent): no structure theory for
  (L3).
  - Dimension counting fails: `F_2 x F_2` has `cd = 2` and is incoherent.
  - Hyperbolicity fails: Rips's construction gives hyperbolic groups with
    finitely generated, not finitely presented subgroups, so Anosov structure
    alone gives nothing.
