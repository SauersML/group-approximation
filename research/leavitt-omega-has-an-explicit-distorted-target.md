---
rg: 2
id: leavitt-omega-has-an-explicit-distorted-target
kind: claim
title: The hidden qp relation fails explicitly on x13(s0) and the cycle packet
artifacts:
  - research/leavitt-omega-has-an-explicit-distorted-target-proof.md
  - research/artifacts/verify-leavitt-nielsen-collision-red-team.py
distinct_from:
  leavitt-nielsen-collision-has-a-hidden-first-side-relation: that proves Omega(a,qp)=1; this gives a shortest clean pair on which the same two-variable law is nonidentity.
  leavitt-hidden-face-three-gate-retractions: that fences the existing collision from transporting Omega; this isolates exactly what a successful two-cell transport would have to kill.
  kl-violating-equation-over-leavitt-unit-group: that requires one nonsingular equation to force the target relation; the target distortion alone is not such a compiler.
---

For

```text
Omega(X,Y)=[X,Y^2XY^(-2)],
```

the source pair `a=x_12(s_0)`, `r=qp` satisfies `Omega(a,r)=1`.  In the same
Leavitt elementary group take

```text
A=x_13(s_0),      B=p=(1 2 ... 20).
```

Then

```text
Omega(A,B)=x_15(s_0^2) != 1.
```

Thus simultaneous transport of `(a,r)` to `(A,B)` would give an explicit
one-copy coefficient kernel.  The identity and nonidentity are both checked
symbolically on the faithful infinite-word Leavitt module.
