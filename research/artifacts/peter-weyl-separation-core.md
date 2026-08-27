# Finite-dimensional unitary representations separate points of a compact group

Former Cairn claim `peter-weyl-separation-core`, demoted because its own audit
places this classical formalization gap outside every active program route.

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

## Why this sits off the root graph

The consumer is a statement the graph does not carry.  With separation, the
five approximation radicals coincide for general compact targets; that general
statement has no node.  What the graph does have is
[[bohr-residual-equals-finite-residual-for-profinite-targets]], the profinite
case, which is unconditional and needs nothing from here, and
[[compression-wreath-five-radicals-coincide]], which is established by squeezing
against a residually finite target and likewise never separates a compact group.

So this hole is real but nothing is currently blocked on it.  Adding a node for
the general-target statement would produce a second detached top rather than a
path, so the right time to add it is when something in the program actually
needs a compact target that is not profinite.
