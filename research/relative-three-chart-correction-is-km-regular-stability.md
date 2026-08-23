---
rg: 2
id: relative-three-chart-correction-is-km-regular-stability
kind: claim
title: Relative simultaneous correction of the three Kac-Moody charts is exactly regular-branch stability
distinct_from:
  kernel-section-builds-relative-p13-chart: that constructs an approximate P13 chart agreeing with the tree side before finite-group exactification; this proves that exactifying all three charts relatively is the terminal global correction problem.
  finite-face-flatness-stops-at-fundamental-group-holonomy: that classifies bare face-flat unitary connections; this uses the actual triangle-of-finite-groups universal property and the absence of nontrivial finite-dimensional representations.
  compact-hyperbolic-km-regular-microstates-synchronize: that states global regular-microstate correction; this gives its exact equivalent formulation in terms of the three finite rank-two charts.
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
