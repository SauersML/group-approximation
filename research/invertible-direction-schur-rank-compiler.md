---
rg: 2
id: invertible-direction-schur-rank-compiler
kind: claim
title: Every Boolean predicate has a Schur rank compiler with invertible selector derivatives
artifacts:
  - experiments/invertible_direction_schur_compiler.py
  - experiments/invertible-direction-schur.json
distinct_from:
  boolean-predicate-is-one-rank-jump: that gives an affine one-rank jump with an everywhere-invertible leading block; this additionally makes every selector coefficient of that leading block invertible.
  every-predicate-has-s3-equivariant-raw-radical-drop: that equips a rank-drop radical with an S3 action; this preserves the rank-up Schur orientation and regularizes every selector direction for a scale-preserving reset.
  support-failure-has-fixed-pivot-rank-one-compiler: that optimizes one two-bit predicate for size; this gives one universal baseline pencil for every predicate of a fixed arity.
---

For every `k>=1` there are an effectively constructible integer

```text
N=k 2^k,
```

an affine matrix pencil

```text
U_k(x)=U_0+sum_(i=1)^k x_i U_i in M_N(F_2),             (IDS1)
```

and a fixed column `v` such that

```text
U_k(x) is invertible for every x in F_2^k,
U(v)=sum_i v_i U_i is invertible for every nonzero v.    (IDS2)
```

For every Boolean predicate `f:F_2^k->F_2` one can effectively choose a row
`u_f` so that

```text
M_f(x)=[[U_k(x),v],[u_f,0]],
rank_F2 M_f(x)=N+f(x).                                    (IDS3)
```

The leading packet `A_k=K(U_k)` is independent of `f`.  In every selector
sector it has one spin simple of dimension `D=2^N`.  The full packet
`B_f=K(M_f)` restricts to that baseline with multiplicity one when `f(x)=0`
and multiplicity two when `f(x)=1`, exactly as in the original Schur
compiler.  The additional conclusion `(IDS2)` says that the discrete
derivative in **every nonzero** selector direction is another nondegenerate
spin form of the same dimension `D`. This includes the two-share gauge
direction `(1,1)`.

For a finite menu of predicates of arity at most `k`, use the same `U_k` and
pad every predicate by ignored selector bits.  Thus all predicates have one
literal common baseline group, not merely isomorphic baseline matrix
algebras.  This is useful for context return: changing the predicate changes
only the last Schur row, while every selector direction retains a full-rank
reset form.

The exact verifier finds smaller explicit pencils for the arities used by the
factored Fanizza menu.  In particular one affine pencil of size `16` works for
all predicates of arity at most four; its sixteen reciprocal evaluation
vectors form an `F_2` basis.  This yields the uniform fixed spin scale
`D=65536`.  The general theorem does not depend on that search.
