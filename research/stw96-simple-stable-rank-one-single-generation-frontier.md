---
rg: 2
id: stw96-simple-stable-rank-one-single-generation-frontier
kind: claim
title: Every unital simple separable stable-rank-one C*-algebra is singly generated
root: true
distinct_from:
  stw99-problem-xcvi-simple-single-generation: the Elliott-Li-Niu counterexample refutes the unrestricted claim but has stable rank at least two.
artifacts:
  - research/artifacts/stw96-regular-rank-single-generation-audit-2026-08-30.md
---

Does every unital simple separable C*-algebra of stable rank one have a single
generator?

This remains open.  Elliott--Li--Niu, Proposition 3.3, compute their
counterexample's ranks as

```text
2 <= tsr(A) <= 4,       2 <= rr(A) <= 3,
```

and explicitly isolate stable rank one as the next frontier.  Existing
positive theorems cover Z-stable algebras, AF algebras, graph algebras, and
several classifiable subclasses, but do not cover arbitrary simple
stable-rank-one algebras.

## Attempts

The Thiel--Winter coding argument uses the approximately central tensorial
room supplied by a unital copy of `Z`; stable rank one alone gives density of
invertibles and projection cancellation, but no such orthogonal central
coding family.  Conversely, the Elliott--Li--Niu Thom--Porteous obstruction
cannot simply be retained while lowering stable rank: their same nonzero
topological cycle proves `tsr(A)>=2`.  A solution therefore needs either a
new coding mechanism extracted from stable rank one or an obstruction not
tied to that cycle.

The quotient-transfer route is also closed exactly by
`stw96-quotient-obstructions-preserve-rank-defects`: stable rank one passes to
quotients, so any quotient whose failure of single generation obstructs the
ambient algebra would itself already be a stable-rank-one counterexample.  In
particular no extension, character-tensor amplification, or obstructed-fibre
construction retaining the Elliott--Li--Niu quotient can lower the stable rank
to one.
