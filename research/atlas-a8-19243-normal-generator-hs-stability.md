---
rg: 2
id: atlas-a8-19243-normal-generator-hs-stability
kind: claim
title: Small 19243 translation defect kills all nontrivial A8 representation mass
artifacts:
  - experiments/atlas_a4_19243_normal_closure.py
---

Let `b in A8 ~= GL_4(F2)` be the repeated first-chart involution occurring in
collision `q_19243`.  There is a constant `C_19243<infinity`, depending only on
this fixed element of `A8`, such that for every finite-dimensional exact unitary
representation

```text
pi : A8 -> U(d)
```

with invariant-space projection `Q_pi`,

```text
tr_d(1-Q_pi)
 <= C_19243 ||pi(b)-1||_2^2.                           (A8-19243-STAB)
```

Consequently, in arbitrary external multiplicity, `pi_n(b)->1` forces the
normalized dimension of every nontrivial `A8` sector to tend to zero.

This is the quantitative representation-theoretic advantage of compiling the
A4 packet holonomy all the way to the **full chart group** rather than stopping
inside the affine parabolic.  By `atlas-a4-19243-parabolic-normal-closure`, the
same conclusion is false at the normal-closure level in `P=AGL_3(2)`: killing
`b` there leaves an entire `GL_3(2)` quotient.

## Attempts

- Combine the exact audit `<<b>>_A8=A8` with the general finite normal-generator
  Hilbert--Schmidt trivialization theorem.
