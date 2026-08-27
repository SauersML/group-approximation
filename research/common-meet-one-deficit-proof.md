---
rg: 2
id: common-meet-one-deficit-proof
kind: route
title: Keep the exact meet codimension in the one-Gram estimate
target: common-meet-local-sectors-pay-one-deficit
requires:
  - high-density-local-sectors-force-one-bcs-gram
---

The proof of the high-density theorem already constructs `p=meet_c q_c`.
Do not replace its exact deficit by the union bound.  Since
`tr(p)=1-beta`, for every Bob involution `B` the orthogonal off-diagonal
corners give

```text
||[B,p]||_2^2<=2 beta.                                      (CMP1)
```

Right compression still gives

```text
||F_c p||_2<=epsilon_c,
||(A_(c,x)-B_x)p||_2<=kappa_(c,x).                          (CMP2)
```

Using

```text
A_(c,x)p-pB_x=(A_(c,x)-B_x)p+[B_x,p]                       (CMP3)
```

and the squared triangle inequality, the consistency contribution is at
most `(1/2)kappa_(c,x)^2+beta`.  The question weights have total mass one,
so the one-Gram energy is bounded above by the right side of `(CMD2)`.
The finite BCS gap bounds it below by `Delta tr(p)=Delta(1-beta)`.  This
proves `(CMD2)` and hence `(CMD3)`.

