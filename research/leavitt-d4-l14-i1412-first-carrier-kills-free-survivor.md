---
rg: 2
id: leavitt-d4-l14-i1412-first-carrier-kills-free-survivor
kind: claim
title: The first inverse carrier equation kills the free third-carrier boundary
artifacts:
  - research/artifacts/enumerate-l14-i1412-eq1-maximal.py
  - research/leavitt-d4-l14-i1412-first-carrier-kills-free-survivor-proof.md
distinct_from:
  leavitt-d4-l14-i1412-has-free-rank-three-one-copy-survivor: that solves the third carrier equation alone; this imposes the omitted first carrier equation and computes its exact residual.
  leavitt-revised-degree4-candidate-is-injective: that proves injectivity for a different revised degree-four word via gate factors; this is a direct compatibility calculation for the inverse length-fourteen picture scheme.
---

For the explicit free-rank-three solution of the inverse `1;412` third
carrier equation, the independently expanded first carrier equation reduces
to exactly the candidate outer boundary:

```text
Eq1 residual = (Q P^-1)_3 = K.
```

Consequently the full carrier system forces `P=Q` and `K=1`.  In particular
there is no specialization of this scheme sending `QP^-1` to a nontrivial
Leavitt mark while retaining all carrier equations.  The 15-block scheme is
a valid half-picture, not a Kervaire--Laudenbach relative picture and not an
injectivity counterexample.

