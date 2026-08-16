---
rg: 2
id: literal-orbital-graph-block-clique
kind: claim
title: Each block of the literal orbital graph is a complete subgraph
distinct_from:
  literal-lamp-kernel-clifford-block-amalgam: That claim is the full amalgam decomposition of the lamp kernel, including the free-product structure over the blocks; this is the single graph-theoretic input it rests on, isolated because it is the only part still unproved and because it is what identifies the two presentations.
  literal-telescope-split-normal-form: That identifies the vertical quotient and the splitting; this says nothing about the vertical group and everything about the edge relation on sites.
artifacts:
  - docs/LITERAL_ORBITAL_CLIQUE_ROUTE.md
  - GroupApproximation/Sofic/LiteralBlockNormalForm.lean
---

For the literal group's orbital graph on sites `X = V/B`,

```text
Adjacent xi eta  <->  blockOf xi = blockOf eta  and  xi <> eta .
```

**Half proved, 2026-08-16.**  The forward direction is
`LiteralBlockNormalForm.blockOf_eq_of_adjacent`: an edge never leaves a block,
because the marked pair shares a block and the edge relation is a translate
while `blockOf` is equivariant.  With it,
`not_adjacent_of_blockOf_ne` — lamps at sites of different blocks commute
outright rather than through the sign.

**The converse is open.**  It says the block subgroup acts two-transitively on
the eight sites of a block, which factors as simple transitivity of the
translations on the parity group `(Z/2)^3` together with transitivity of the
rotations on the seven nonzero parities.  The second input already exists in
another guise — it is the `x, x^2, z, yz, yx, y^2x` fact that
`Sofic/LiteralSignFreeQuotient.lean` uses to reduce every parity commutator to
a conjugate of the mark.  What is missing is the parity apparatus at the level
of sites rather than of the base; `docs/LITERAL_ORBITAL_CLIQUE_ROUTE.md` names
the three definitions required.

**Why it is isolated here.**  It is the last graph-theoretic input between the
normal form and the soficity tower, and it was repeatedly mistaken for a
formalization task.  It is a theorem nobody has proved, in Lean or on paper.
An attempt on 2026-08-16 produced a module whose proofs referenced six lemmas
that do not exist; it was deleted rather than committed.
