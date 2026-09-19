---
rg: 2
id: leavitt-degree-four-affine-omega-candidate
kind: claim
title: A length-eight degree-four Leavitt word supplies a full-support affine Omega transport system
artifacts:
  - research/leavitt-degree-four-affine-omega-candidate-proof.md
  - research/artifacts/verify-leavitt-degree-four-affine-omega-candidate.py
distinct_from:
  leavitt-transport-drift-and-l7-atomic-no-go: that exhausts the literal minimal atomic compiler; this adds a fourth translated relator and a nonlinear affine feedback orbit.
  leavitt-omega-has-an-explicit-distorted-target: that identifies the one-copy root which transport must kill; this constructs a nonsingular full-support word whose orbit ratios can be tested for that transport.
  kl-violating-equation-over-leavitt-unit-group: that requires a proved one-copy coefficient kernel; this records the exact candidate system and explicitly leaves that kernel derivation open.
---

Let `r=qp` and `c=x_13(s_0)`.  The word

```text
W_8=r t^2 a t^(-1)c t^2 e t^(-1)q t p t
```

has `t`-length eight, degree four and full Leavitt coefficient support.  Its
four cyclic sign-change coefficients are the involutions `a,c,e,q`, while
the infinite packets `r,p` occur only inside positive runs.

Its four index-four relators consist of one explicit affine pivot and three
zero-drift feedback relations.  This is the first concrete system beyond the
degree-three atomic transport fence with enough relation rank to attempt
simultaneous transport of `Omega(a,qp)=1` to the distorted pair
`(x_13(s_0),p)`.

The construction is established; whether the feedback relations actually
kill `Omega(x_13(s_0),p)=x_15(s_0^2)` remains open.
