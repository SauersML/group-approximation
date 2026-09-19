---
rg: 2
id: mf-refutation-yields-nonhyperlinear-group-proof
kind: route
title: A counterexample is a nonhyperlinear group by definition
target: mf-refutation-yields-nonhyperlinear-group
requires: []
---

## Direct proof

`mf-implies-hyperlinear` asserts that every MF group is hyperlinear.  A
refutation is a group `G` which is MF and not hyperlinear.  The second half
of that data is precisely the statement of `non-hyperlinear-group`, and the
witness is explicit whenever the refutation is.  End proof.

The converse direction is not asserted: a nonhyperlinear group need not be
MF, and indeed the only currently available nonhyperlinearity mechanisms in
this repository (finite-multiplicity synchronization, the Leavitt--Steinberg
stability fork) produce candidates whose MF status is unknown.
