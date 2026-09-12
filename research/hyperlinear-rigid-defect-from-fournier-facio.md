---
rg: 2
id: hyperlinear-rigid-defect-from-fournier-facio
kind: route
title: A hyperlinear Fournier--Facio group is a hyperlinear group with a nontrivial rigid defect
target: hyperlinear-group-carries-nontrivial-rigid-defect
requires:
  - fournier-facio-group-hyperlinear
  - fournier-facio-group-carries-rigid-defect
---

Take `H = G`.  The rigid pair `Gamma <= G` has a nontrivial defect, so a
hyperlinear `G` is exactly the witness the target asks for.

Its Question 3.4 consequence, through
`hyperlinear-nonsofic-via-hyperlinear-rigid-defect`, coincides with
`hyperlinear-nonsofic-from-fournier-facio`.  What this route adds is that the
positive branch for `G` refutes `hyperlinear-groups-kill-rigid-compression-defects`,
and with it every nonhyperlinearity conclusion drawn from that criterion.
