---
rg: 2
id: wall-rigid-z2-sft-is-quantum-rigid
kind: claim
title: Every wall-rigid Z^2 subshift of finite type is quantum rigid, so its crossed-product algebra is finitely presented
distinct_from:
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that proves wall rigidity equals the first-order part of quantum rigidity; this asks whether the first-order part is everything, that is whether an idempotent commutator ideal of the local tiling algebra must vanish.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one free minimal instance; this is a general local-to-global principle which, with labbe-shift-is-wall-rigid, would give that instance.
---

**OPEN.** Let `Ω` be a `Z^2`-SFT that is `D`-wall-rigid, meaning every difference set of two of its points is
`2D`-connected. Then `Ω` is `D'`-quantum rigid for some `D'`. Equivalently
(`sft-wall-rigidity-iff-idempotent-commutator-ideal`), the idempotent commutator ideal `J_(D')` of the local
tiling algebra vanishes.

**Payoff.** With `labbe-shift-is-wall-rigid`, it gives
`labbe-wang-shift-crossed-product-is-finitely-presented`, and hence gate (a) of the ring route.

**Refutation.** A wall-rigid SFT with a contextual operator family: noncommuting, with no two-dimensional
composition factor. Examples would be a periodic quantum tiling of an aperiodic wall-rigid shift
(`periodic-quantum-tilings-refute-quantum-rigidity`), or a non-abelian solution group below.

## Attempts

- **First order: done.** Walls are exactly the extension-type obstructions
  (`sft-wall-rigidity-iff-idempotent-commutator-ideal`). What remains is idempotent noncommutativity, visible
  only in irreducible families of dimension `>= 3` or in modules without finite filtrations.
- **Group shifts: holds, conditionally on Bieri–Strebel (recalled).**
  - The crossed product of a group shift is the group algebra of its lamp group, so a finitely presented
    lamp group gives rigidity (`group-shift-crossed-product-fp-from-lamp-group-fp`).
  - Antipodal one-sided configurations give walls (`antipodal-one-sided-group-shift-configurations-are-walls`).
  - Bieri–Strebel says the lamp group is finitely presented iff `Σ^c` has no antipodal pair (recalled,
    Proc. LMS 1980, not re-read). With it, a group shift is wall-rigid iff it is quantum rigid.
  - So for algebraic shifts this claim is the Bieri–Strebel theorem, with walls as antipodal points of
    `Σ^c`.
- **Tree covers of classical pieces: done.** Families glued from classical tilings along separating bands
  commute under wall rigidity. On each band block, "agree on side 1" and "agree on side 2" cover all pairs,
  so one of them is complete, and the transition splits
  (`research/artifacts/quantum-rigidity-group-shifts-and-gluing-2026-09-13.md`, Proposition P2).
- **Cyclic covers: live, and where freedom could come from.** Non-separating bands evade P2.
  - In dimension 3, hand checks found three- and four-step frame loops closing trivially, and triangles
    through a scalar ray producing walls. Frame-changing bands cannot end at a coarse vertex with a
    complementary band.
  - Kochen–Specker triads in dimension 3 on non-simply-connected arrangements are not excluded. The magic
    square suggests dimension `>= 4`.
- **Labbé's shift as the test case (heuristic).** It has fault lines in four directions, so half-plane
  determinism fails antipodally in four directions, which is not Bieri–Strebel tame. Yet it has no walls
  (`labbe-shift-is-wall-rigid`).
  - For group shifts the two conditions coincide, through superposition. Labbé's shift separates them.
  - The hard direction of Bieri–Strebel propagates relations by one-sided determinism, which Labbé's shift
    lacks. So a proof there needs a different mechanism: crossing fault networks.
  - Piecewise-classical families for Labbé's shift split over torus points and commute, provided agreement
    on a thick unbounded band pins the torus point. That is not fully checked along rational directions.
- **Where a proof must go.** A counterexample must be non-piecewise-classical at every scale: local frames
  change with no gauge region carrying a constant classical decomposition. In game terms, this is
  contextuality on a planar arrangement of heavily overlapping contexts, where Arkhipov's planarity theorem
  (recalled) does not directly apply.
