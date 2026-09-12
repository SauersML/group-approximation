---
rg: 2
id: every-predicate-has-s3-equivariant-raw-radical-drop
kind: claim
title: Every Boolean predicate has an S3-equivariant raw radical rank-drop packet
artifacts:
  - experiments/s3_equivariant_radical_compiler.py
  - experiments/s3_equivariant_and_radical_phase_packet.py
distinct_from:
  boolean-violation-is-one-raw-radical-qubit-drop: that exposes two fixed radical words but has no symmetry relating their three nonzero directions; this makes that radical the natural S3-module in every forbidden sector.
  six-generator-one-jump-router-has-s3-radical-atlas: that finds an S3 orbit in one two-selector rank pencil; this gives an effective compiler for every Boolean predicate.
  phase-inverting-fourth-root-lifts-opposite-pauli-shears: that repairs one constant Pauli plane; this adjoins roots of every affine central selector coefficient and lifts the whole predicate packet symmetry.
---

Let `f:{0,1}^k->{0,1}` be nonzero.  There is an effectively constructible
affine alternating matrix `A_f(x)` of size `4N`, with `N=k|f^(-1)(1)|` for
`k>0`, such that

```text
rank A_f(x)=4N-2f(x).                                         (SER1)
```

For every forbidden assignment `a`, the radical of `A_f(a)` has a fixed
basis `r_(a,0),r_(a,1)` consisting of zero-one vectors independent of the
selector values.  One group `S3=GL_2(F_2)` acts coefficientwise by isometries
of the entire affine pencil, and its action on every hot radical is the
natural two-dimensional representation.  In particular it is transitive on

```text
r_(a,0), r_(a,1), r_(a,0)+r_(a,1).                            (SER2)
```

For the associated class-two packet, adjoin a central fourth root of `J` and
of every central selector involution.  The two standard transvections in
`S3` then lift to involutive packet automorphisms: correct each image generator
by the product of central roots whose square is its quadratic defect, and
invert all central roots.  The product of the two lifts has order three.
Thus `(SER2)` is symmetry by ordinary finite-group automorphisms, not merely
an isometry of sector commutator forms.

The construction is explicit.  Start with the literal-cycle matrix `C_f`
from `(BRD10)`.  Let `D` have one diagonal `1` on each forbidden block and
put

```text
S_f=[[0,C_f],[C_f^T,D]],             A_f=H tensor S_f,
H=[[0,1],[1,0]].                                             (SER3)
```

On a satisfying assignment, `S_f` is invertible.  On a forbidden assignment
it has corank one, with a fixed all-one block kernel.  The outer `H` factor
therefore supplies exactly the natural radical plane in `(SER2)`.

For the binary AND violation this specializes to the four-generator form

```text
H tensor [[x,1],[1,y]],                                      (SER4)
```

with rank profile `4,4,4,2`.  The second artifact symbolically audits its
central roots, both lifted involutions, their order-three product, and the
hot radical orbit.

## Attempts

- The affine-rank and phase-root construction is explicit.  The deferred
  problem is global: force an arbitrary finite-dimensional approximation to
  use the three conjugate radical directions coherently in one return cycle.
