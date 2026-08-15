---
rg: 2
id: mf-refutation-yields-nonhyperlinear-group
kind: claim
title: Refuting MF implies hyperlinear solves the nonhyperlinear target
distinct_from:
  non-hyperlinear-group: That claim is the program target itself; this one records that one branch of the MF-to-hyperlinear bridge is at least as hard as it.
  mf-implies-hyperlinear: This claim is about the cost of the negative branch of that root, not about the root's truth value.
---

Any counterexample to `mf-implies-hyperlinear` is by definition an MF group
that is not hyperlinear, hence establishes `non-hyperlinear-group`, the
program's primary target.  Therefore the refutation branch of the bridge is
at least as hard as the whole nonhyperlinearity program, and effort spent on
the bridge should be spent on the positive branch: partial theorems, and
identification of the exact analytic input.

Symmetrically, `mf-implies-hyperlinear` cannot be refuted "cheaply" by any
argument that does not also produce a nonhyperlinear group; in particular no
counting, index, or invariant argument can do it
(`invariant-size-collapse`, `trace-blindness-sharpness`).
