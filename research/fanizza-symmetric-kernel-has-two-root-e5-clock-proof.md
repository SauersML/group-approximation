---
rg: 2
id: fanizza-symmetric-kernel-has-two-root-e5-clock-proof
kind: route
title: Move the symmetric cross relation on only one E5 block
target: fanizza-symmetric-kernel-has-two-root-e5-clock
requires:
  - fanizza-bad-atoms-have-symmetric-frames
  - free-root-top-boundary-reservoir-is-summable
artifacts:
  - experiments/fanizza_symmetric_kernel_e5_clock.py
---

The two determinant lines `e_01` and `e_23` are fixed because `det S=1` and
the second block is the identity.  Identify the four cross wedges with a
two-by-two matrix.  Left multiplication sends the matrix
`J=[[0,1],[1,0]]` of `e_03+e_12` to

```text
S^n J=[[c_n,a_n],[d_n,c_n]],
```

which is `(SKE1)`.  The standard degree induction for powers of `S` gives
`deg(a_n,c_n,d_n)=(2n,2n-1,2n-2)`, proving `(SKE2)` and pairwise transverse
moving lines.

Multiplying the two elementary matrices in `(SKE3)` gives the stated block
diagonal matrix directly.  Pulling the identity cross form `H` through its
four-coordinate action gives degree profile

```text
(-1,2n,2n-1,2n-1,2n-2,-1)
```

after cancellation with the level-zero copy.  Only `e_02^*` reaches degree
`2n`, proving the rank-one boundary pulse.

For `(SKE4)`, represent the quotient by `K_0` with commutator columns

```text
(0,e_0,e_1,e_1,e_2,0)
```

in wedge order `(01,02,03,12,13,23)`.  Precompose the source half with
`wedge^2(T_L^n)` and retain an untransported coefficient half.  Exact
polynomial elimination over `F_2[x]` gives determinantal divisors
`(1,1,1,c_n)`.  The verifier checks the E5 matrices, kernel orbit, unique top
coefficient, fraction-field ranks, all maximal-minor gcds, and all pairwise
kernel intersections through 48 levels.
