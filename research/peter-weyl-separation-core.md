---
rg: 2
id: peter-weyl-separation-core
kind: claim
title: Finite-dimensional unitary representations separate the points of a compact group
artifacts:
  - GroupApproximation/Analysis/PeterWeylProfinite.lean
---

OPEN, and isolated in Lean as the single named hypothesis
`Analysis.PeterWeylProfinite.SeparatesPoints`: for a compact Hausdorff
topological group and a nonidentity element, some continuous finite-dimensional
unitary representation does not kill it.

This is the one classical import behind the dossier's Bohr clauses (sections
46.5 and 49.12).  With it, `fdUnitaryResidual_le_bohrResidual_of_separates` and
`linearResidual_le_bohrResidual_of_separates` supply the inclusions that make
all five radicals coincide; without it, the profinite case is still
unconditional -- see
[[bohr-residual-equals-finite-residual-for-profinite-targets]].

## An inventory, because an earlier version of the file guessed and guessed wrong

**Present in Mathlib**: Haar measure on a compact group; the spectral theorem
for compact self-adjoint operators, with finite-dimensionality of the
eigenspaces (`Analysis/InnerProductSpace/Spectrum`); Arzelà--Ascoli
(`Topology/ContinuousMap/Bounded/ArzelaAscoli`).

**Absent**: continuity of translation in `L^2`; convolution on a general
compact group -- `Analysis/Convolution` is written for additive groups and
normed spaces, not for Haar convolution on a possibly nonabelian compact group;
and, resting on those two, compactness of the convolution operator.

That last item is the whole gap, and it is [[haar-convolution-operator-is-compact]].
So the remaining work is one analytic lemma plus the convolution API it needs,
not a missing theory of compact groups.
