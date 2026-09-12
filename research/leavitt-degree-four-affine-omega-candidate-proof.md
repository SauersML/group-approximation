---
rg: 2
id: leavitt-degree-four-affine-omega-candidate-proof
kind: route
title: Put both infinite packets inside positive runs and compute the four affine orbit relators
target: leavitt-degree-four-affine-omega-candidate
requires:
  - leavitt-transport-drift-and-l7-atomic-no-go
  - leavitt-omega-has-an-explicit-distorted-target
---

Put

```text
a=x_12(s_0),       e=x_12(t_1),
q=x_34(s_1)x_(11,12)(t_0),
r=qp,              c=x_13(s_0).
```

Consider the length-eight, degree-four word

```text
W_8=r t^2 a t^(-1)c t^2 e t^(-1)q t p t.            (A8.1)
```

Its sign type is `++-++-++`, with coefficient slots

```text
(r,1,a,c,1,e,q,p).                                  (A8.2)
```

The four cyclic sign-change coefficients are exactly `a,c,e,q`.  They are
nontrivial involutions: `a,c,e` are characteristic-two elementary roots, and
the two disjoint factors of `q` commute.  The two infinite packets `r,p` lie
strictly inside same-sign positive runs.  Thus `(A8.1)` avoids the immediate
infinite-order sign-gate fence which kills the naive two-conjugacy gadget.

The coefficients have full Leavitt support.  Indeed `p` and `r=qp` recover
`q=rp^(-1)`, and the established generation proof for `{a,e,q,p}` then gives
all of `EL_20(L_(F_2)(1,2))`; `c` is redundant.

In the index-four kernel, with `z=t^4`, the four translated relators are

```text
R_0=r_0 a_2 c_1 e_3 q_2 p_3 z,
R_1=r_1 a_3 c_2 z e_0 z^(-1)q_3 z p_0,
R_2=r_2 z a_0 z^(-1)c_3 z e_1q_0p_1,
R_3=r_3 z a_1c_0e_2q_1p_2.                          (A8.3)
```

The first is an affine pivot:

```text
z=p_3^(-1)q_2e_3c_1a_2r_0^(-1).                    (A8.4)
```

Substitution into the other three relators produces the maximal rank-three
zero-drift system permitted by the lower bound in
`leavitt-transport-drift-and-l7-atomic-no-go`.  Unlike a direct test-word
conjunction, two of the remaining relators contain alternating positive and
negative occurrences of the common affine pivot; the fourth closes the
feedback orbit.

This is an exact candidate construction, not yet a KL violation.  The
required next statement is

```text
Omega(c_0,p_0)=x_15(s_0^2)_0 in <<R_0,R_1,R_2,R_3>>,
```

using `Omega(a_i,r_i)=1` in each coefficient copy.  No such derivation has
yet been established, and no claim of coefficient collapse is made here.
