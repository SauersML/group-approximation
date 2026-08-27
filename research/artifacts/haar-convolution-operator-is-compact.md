# Convolution by a continuous function on a compact group is compact on L-two

Former Cairn claim `haar-convolution-operator-is-compact`, demoted with its
off-program Peter--Weyl formalization lane.

OPEN, and it is the entire analytic gap behind
[[peter-weyl-separation-core]].  For a compact Hausdorff group with Haar
measure and a continuous `f`, the operator

    (T_f x)(g)  =  integral over the group of  f(g h^{-1}) x(h)  d h

on `L^2` is compact.

Two prerequisites are missing from Mathlib and are part of this claim:
continuity of translation in `L^2`, and Haar convolution on a possibly
nonabelian compact group -- `Analysis/Convolution` is written for additive
groups and normed spaces.  Given those two, compactness follows the usual way:
uniform continuity of `f` on a compact group makes the kernel uniformly
approximable, and Arzelà--Ascoli (which Mathlib has) supplies the compactness.

## Why it is stated separately from the separation statement

Because it is the only genuinely analytic ingredient, and everything above it
is formal: given compactness, convolution by a bump has finite-dimensional
eigenspaces by the spectral theorem, those eigenspaces are translation
invariant, and translating into them separates the point at hand.  Keeping the
two apart is what makes it possible to say that the repository's Bohr clauses
rest on one lemma with a proof strategy, rather than on "Peter--Weyl".
