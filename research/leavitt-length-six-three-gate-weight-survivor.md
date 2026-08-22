---
rg: 2
id: leavitt-length-six-three-gate-weight-survivor
kind: claim
title: A full-support length-six Leavitt equation has a third involution gate and defeats the relative aspherical weight test
distinct_from:
  leavitt-length-six-full-support-torsion-candidate: That candidate has only the two forced torsion gates and is fenced by a relative weight function; this changes the middle coefficient packet so a third admissible square makes such a weight impossible.
  leavitt-paired-quotient-passes-relative-weight-test: That proves coefficient injectivity for the first paired quotient; this is the first explicit same-length paired quotient not covered by that proof.
artifacts:
  - research/leavitt-length-six-three-gate-weight-survivor-proof.md
  - research/artifacts/verify-leavitt-length-six-three-gate-survivor.py
---

Let `a=x_12(s_0)`, `e=x_12(t_1)`, `p=(1 2 ... 20)`, and put

```text
q=x_34(s_1)x_(11,12)(t_0).
```

In `G=EL_20(L_(F_2)(1,2))`, consider

```text
W=a t^2 q t p t e t^(-2).                           (L6G.1)
```

This is the `++++--` word with coefficient slots `(a,1,q,p,e,1)`.  Its
nonidentity coefficients generate all of `G`, and the coefficients at the two
cyclic sign changes are the involutions `a,e`.

In the degree-two kernel, its paired relative presentation has a third
admissible square at the zero-weight edge `h_0=a_0`.  No aspherical
Bogley--Pride weight function exists for this star graph.  Thus the global
weight argument which proves injectivity for the previous candidate cannot
fence `(L6G.1)`.

The specialization `t=1` is not a solution, and neither retraction obtained
by killing one coefficient copy exists.  Whether the paired relators have a
coefficient kernel remains open; this claim is an explicit survivor of the
length-six weight and elementary-retraction screens, not a KL violation.

