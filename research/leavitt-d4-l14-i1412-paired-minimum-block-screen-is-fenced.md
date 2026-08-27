---
rg: 2
id: leavitt-d4-l14-i1412-paired-minimum-block-screen-is-fenced
kind: claim
title: Every one-copy boundary in the paired minimum-block inverse screen is trivial
artifacts:
  - research/artifacts/enumerate-l14-i1412-carrier-pairs.py
  - research/artifacts/enumerate-l14-i1412-boundary.py
  - research/leavitt-d4-l14-i1412-paired-minimum-block-screen-is-fenced-proof.md
distinct_from:
  leavitt-d4-l14-i1412-first-carrier-kills-free-survivor: that kills one explicit free Eq3 half-picture; this covers every simultaneous carrier state produced by the two corrected minimum-block screens.
  leavitt-d4-l14-n0511-is-fenced: that globally fences every branch of the normal class; this result is deliberately restricted to globally minimum-block schemes in the inverse class.
---

Intersect the corrected globally minimum-block noncrossing schemes for the
third and first carrier equations of inverse class `1;412`, preserving the
twelve original coefficient coordinates.  For every cyclic cut and every
target coefficient copy, every resulting one-copy boundary is trivial in
the associated coefficient quotient.

The exact screen has 43 simultaneous carrier states, 195 boundary states,
and 18 syntactically nonempty target images.  Fourteen are cyclic conjugates
of defining relators.  Each of the remaining four quotients contains both
`x6^2=1` and `x6^3=1`; its target is `x6^6` or a conjugate.  Hence those four
targets are also trivial.

This closes the paired **minimum-block** sector only.  A class-wide inverse
fence still requires non-minimal cancellation schemes; no claim about them
or about non-hyperlinearity is made.

