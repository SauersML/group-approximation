---
rg: 2
id: relative-three-chart-correction-is-km-regular-stability
kind: claim
title: Relative simultaneous correction of the three Kac-Moody charts is exactly regular-branch stability
distinct_from:
  kernel-section-builds-relative-p13-chart: that constructs an approximate P13 chart agreeing with the tree side before finite-group exactification; this proves that exactifying all three charts relatively is the terminal global correction problem.
  finite-face-flatness-stops-at-fundamental-group-holonomy: that classifies bare face-flat unitary connections; this uses the actual triangle-of-finite-groups universal property and the absence of nontrivial finite-dimensional representations.
  compact-hyperbolic-km-regular-microstates-synchronize: that states global regular-microstate correction; this gives its exact equivalent formulation in terms of the three finite rank-two charts.
  common-gh-isometry-selects-the-two-overlap-cross-coefficient: that coherently selects the P_1/P_3 overlap gauges near the identity on a 1-o(1) source; this proves the equivalence here begins only at exact simultaneous support invariance, not at an unresolved auxiliary gauge choice.
  relative-finite-group-gh-cannot-fix-two-generating-subgroups: that refutes the generic relative preprocessing theorem which freezes two exact subgroup actions and shows the corresponding alternating Reynolds gap is only quadratic in the local defect; this claim records the stronger Kac--Moody-specific correction still required.
---

**ESTABLISHED.**  Fix the simple Kac--Moody lattice and its native triangle
presentation

```text
Gamma=colim(P_12 <- P_1,P_2; P_13 <- P_1,P_3;
            P_23 <- P_2,P_3).                          (RTC1)
```

On a canonical regular-microstate sequence, use
`kernel-section-builds-relative-p13-chart` together with finite-group
exactification to obtain exact representations of `P_12`, `P_13`, and
`P_23`, each close to its original word table and regular off `o(D)`.
Consider the following remaining assertion:

> after an `o(D)` flexible dimension change and `o(1)` generator
> perturbation, the three exact vertex representations may be chosen, and
> their ambient gauges fixed, so that their restrictions agree exactly on
> `P_1`, `P_2`, and `P_3`.

This assertion is equivalent to
`compact-hyperbolic-km-regular-microstates-synchronize`.

Indeed, exact overlap agreement glues the three vertex representations,
by `(RTC1)`, to a genuine finite-dimensional representation of `Gamma`;
the stated perturbation makes it a correction of the original microstate.
Conversely, any genuine finite-dimensional correction restricts to an
exactly compatible triple with the same bounds.

There is also an exact zero-set obstruction.  No exactly compatible finite
triple can retain a nonzero regular summand of even one nontrivial vertex
group.  Such a triple would glue to a nontrivial finite-dimensional
representation of `Gamma`, whereas an infinite finitely generated simple
group has no nontrivial finite-dimensional unitary representations.

Consequently near-identity multiplicity-cycle holonomy does not leave a
smaller finite semisimple correction lemma.  A dimension-free theorem which
rounds it to exact overlap agreement while preserving positive regular mass
already proves the terminal regular-branch stability statement and hence the
nonhyperlinearity conclusion.  The remaining viable work must establish a
uniform obstruction to such correction, not treat it as a routine last
exactification step.

The identity-gauge audit does remove one apparent preliminary issue.
`common-gh-isometry-selects-the-two-overlap-cross-coefficient` uses the same
normalized-HS Gowers--Hatami isometry to choose the two `P_13` overlap polar
maps with cross coefficient `I+o_2(1)` on `1-o(1)` of the source.  Any far
common target gauge cancels and can be globally conjugated away.  What this
claim calls “relative simultaneous correction” is therefore exactly the
next operation: replace two near-coincident subgroup-invariant supports by
one support invariant under both, and do so consistently around the triangle.
A full-rank scalar phase tending to one shows why deleting `o(d)` dimensions
does not turn near equality into literal equality.  No multiplicity-gauge
choice remains to be optimized before this terminal step.

Nor can generic finite-group stability make that step relative while
freezing the overlap restrictions.  The Pauli packet in
`relative-finite-group-gh-cannot-fix-two-generating-subgroups` is exact and
regular on two generating copies of `C_2`, has defect `delta` on their
commuting relation, and has invertible commutator.  It has no nonzero exact
simultaneous support after any common amplification.  Moreover the natural
two-subgroup alternating conditional expectation has an exact eigenvalue
`1-delta^2/4`; hence there is no defect-independent one-step contraction.
This does not refute a coercive estimate using all native Kac--Moody triangle
relations.  It shows precisely that such an estimate cannot be obtained by
applying a relative Gowers--Hatami lemma or alternating overlap projections
edge by edge.
