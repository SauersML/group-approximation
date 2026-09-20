---
rg: 2
id: compiler-branch-hyperlinear-from-mf-implies-hyperlinear
kind: route
title: The positive rope is MF, so the universal implication covers it
target: mf-compiler-positive-branch-is-hyperlinear
requires:
  - mf-implies-hyperlinear
  - mf-compiler-is-uniform-in-finite-seeds
---

## Why sufficient

For every seed d and e in INF, R_e(d) is operator-MF by
[[mf-compiler-is-uniform-in-finite-seeds]]. Thus the universal
implication [[mf-implies-hyperlinear]], if true, would make every such
output hyperlinear. That premise is now refuted; this is a valid
conditional implication but no longer an available proof route.

## Why this is a genuine reduction, not a restatement

The target concerns **one uniformly constructed family**;
the prerequisite is the universal implication for **every** MF group.  The
prerequisite can fail while the target holds (the rope may be hyperlinear
for its own reasons, for instance by a direct quasidiagonality argument on
the tensor-synchronized trace), so this route does not identify the two.

## Stakes both ways

The prerequisite is a root of the program, and either answer pays:

* if every MF group is hyperlinear, this route closes
  [[hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group]], so
  hyperlinearity of finite presentations is `Pi^0_2`-complete as soon as a
  non-hyperlinear group exists;
* if some MF group is **not** hyperlinear, that group is a witness for the
  program goal [[non-hyperlinear-group]] --- and an MF one, which is the
  most constrained kind of witness the graph has ever asked for.
