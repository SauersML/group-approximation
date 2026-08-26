---
rg: 2
id: five-return-leg-signed-hecke-detector-proof
kind: route
title: Add the two missing actor-endpoint legs and audit adjacent mark scales
target: five-return-legs-cover-signed-hecke-detectors-but-not-source-gauge
requires:
  - middle-pauli-probes-leave-three-hecke-classes-untyped
  - paid-cut-has-moving-hecke-source-or-detector
---

The executable construction and faithful coefficient normal form are those
of `signed-hecke-literal-pauli-probe-audit`.  Retain every exact matrix
commutator from that audit and add the two elementary matrices

```text
L_2=x_12(s_1),                 L_4=x_14(s_1).          (1)
```

For each of the `31` root-free positive classes, range over every element of
the class, all `48` literal dual menu words, and the five second legs in
`(FRC1)`.  The root recognizer requires identity diagonal and exactly one
nonzero off-diagonal coefficient in faithful prefix normal form.  The three
middle legs miss exactly `(MPF4)`.  Neither `L_2` nor `L_4` misses any of
those three.  Conversely their eight misses are disjoint from `(MPF4)`.
The union therefore has zero missed classes, proving `(FRC2)--(FRC3)`.

For exact mark returns, replace `(1)` by the six coefficient-matched legs

```text
x_12(a_m), x_14(a_m),             m=1,2,3.             (2)
```

Compare the full nested commutator matrix with `z=x_13(q)`, not merely with
the elementary-root predicate.  The two `s_1` legs give no exact `z` return
on any of the `31` classes.  Every element in the three old endpoint classes
has exact return profile `{3}` under `(2)`; no element has two adjacent
scales.  Finally, direct conjugation of every matrix in `(2)` by both literal
Whiteheads verifies `(FRC5)`.  This locates the failure at the endpoint
coefficient factor, before any analytic gauge comparison.

The complete deterministic output is frozen in
`experiments/signed-hecke-literal-pauli-probe-results.json`.  MSI jobs
`17035848`, `17036755`, `17038259`, and `17039599` used one CPU; the final
run, including the adjacent-scale sweep, took `00:02:36`.  No experiment
process remains.

Accordingly the next probe should not enlarge the completed finite menu.
It should construct a fresh endpoint-Whitehead `Jhat_(r,m)` satisfying
`(FRC6)` and audit its signed-source normalizer/moving-source multiplicity
action.  The present exact result gives both acceptance tests in advance:
adjacent coefficient transport and a typed occurrence on `R_0 -> P`.
