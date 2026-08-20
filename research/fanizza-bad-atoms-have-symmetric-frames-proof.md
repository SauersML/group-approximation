---
rg: 2
id: fanizza-bad-atoms-have-symmetric-frames-proof
kind: route
title: Exhaust dual baseline words and select a frame-compatible C17 compiler
target: fanizza-bad-atoms-have-symmetric-frames
requires:
  - fanizza-fixed-nonlinear-menu-has-small-rank-gates
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - fanizza-bad-atoms-have-source-fixed-paired-frames
artifacts:
  - experiments/fanizza_partial_center_frame_search.py
---

At a bad atom, the fixed row and column operations from the Schur-pair theorem
put the full matrix in identity form.  Hence any baseline p-word `u` and
q-word `v` with `u dot v=1` are a valid Pauli core at that atom, and contraction
of the affine matrix gives `(SKF2)` by ordinary group-word multiplication.

The verifier enumerates these dual words by increasing total weight.  It first
rejects blocks whose four affine entries do not span a three-dimensional
space.  For every remaining block it computes the six-column commutator map,
checks the coefficient and combined plus/minus kernel equalities, evaluates
the stationary character, and exhausts all coefficient and target characters.
No randomized or floating-point computation occurs.

With the smallest OBDD compiler, C17's atom `(1,0,0)` is the only failure even
after all `496` dual pairs in its five-dimensional baseline are tested.  The
verifier then exhausts the six variable orders.  Orders `(0,1,2)` and
`(0,2,1)` have baseline rank six and solve all four C17 atoms with word weight
at most two.  Fixing the former, while retaining the smallest compilers for
the other predicates, solves all 26 atoms.

For every witness the kernel code expands to the eight vectors in the span
`(SKF3)`.  The script asserts this equality rather than merely comparing
dimensions.  It also exhausts all `20160` matrices in `GL_4(F_2)` and verifies
that no exterior-square word change carries the decomposable support kernel
to `(SKF3)`.  This final negative check prevents silently reusing the wrong E5
transporter.
