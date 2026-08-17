---
rg: 2
id: character-domination-collapse-equivalences-proof
kind: route
title: Compactness in the character, then a permutation-matrix comparison
target: character-domination-collapse-equivalences
requires: []
artifacts:
  - GroupApproximation/Domination/Core.lean
  - GroupApproximation/Domination/Comparison.lean
  - GroupApproximation/Domination/FixedDimension.lean
  - GroupApproximation/Domination/Irreducible.lean
  - GroupApproximation/Domination/PaperStatements.lean
---

## Direct proof, machine-checked

**The equivalences.**  `Domination/Core` proves both in the same shape: "the
character vanishes at `0`" is the qualitative side, "there is a constant `C`
with the linear bound" the quantitative one.  The nontrivial direction is that
no constant forces a sequence of representations whose normalized characters
approach the bad value, which is the contrapositive of the domination
statement; the reverse is immediate.

**The comparison.**  A permutation representation is a unitary representation
whose character counts fixed points, so `Domination/Comparison` reads
`C_perm ≤ C_fd` off the inclusion of permutation matrices into unitaries —
`permutationDomination_of_unitaryDomination`.

**Dimension escape.**  `Domination/FixedDimension` proves domination in each
fixed dimension separately; if all of those hold and the global constant fails,
the witnesses cannot live in any bounded dimension, so a diagonal choice
produces a sequence with dimensions tending to infinity
(`obstruction_requires_matrixDimensionEscape`).  `Domination/Irreducible` runs
the same argument for irreducible degree, using complete reducibility to
reduce a general representation to its irreducible constituents.

No hypothesis on `G`, and no soficity anywhere: the statements quantify over an
arbitrary group, a finite subset and a word.
