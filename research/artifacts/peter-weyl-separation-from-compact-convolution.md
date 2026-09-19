# Spectral theorem on a compact convolution operator, then translation invariance

Former Cairn route `peter-weyl-separation-from-compact-convolution`, demoted
with its off-program formalization lane.

## Why sufficient

Let `c != 1` in the compact group.  Choose a continuous bump `f`, self-adjoint
in the convolution sense, supported near the identity closely enough that
`f` and its left translate by `c` are not equal in `L^2`.  By the prerequisite
the convolution operator `T_f` is compact, and Mathlib's spectral theorem for
compact self-adjoint operators gives an orthogonal decomposition into
eigenspaces, each finite dimensional
(`Analysis/InnerProductSpace/Spectrum`).

Convolution commutes with left translation, so each eigenspace is invariant
under the left regular representation; restricting that representation to one
eigenspace gives a continuous finite-dimensional unitary representation.  If
every such representation killed `c`, then `c` would act trivially on the whole
of `L^2` -- the eigenspaces of a compact self-adjoint operator span the closure
of its range -- contradicting the choice of `f`.  So one of them does not kill
`c`, which is `SeparatesPoints`.

## Why the prerequisite is the whole content

Every step above is either formal or already in Mathlib: the spectral theorem
with finite-dimensional eigenspaces, invariance under translation, and the
density argument.  The prerequisite is the one statement whose proof needs
analysis Mathlib does not have -- and it carries with it the two API gaps
(`L^2` continuity of translation, Haar convolution on a nonabelian compact
group) that the separation statement cannot even be phrased efficiently
without.
