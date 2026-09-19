---
rg: 2
id: lxxiii-via-finite-square-zero-fusion
kind: route
title: Fuse the finite local packet after reserving half the spectral gap
target: problem-lxxiii-global-square-zero-cover
requires:
  - finite-square-zero-packet-covers-cutdown
  - finite-square-zero-packets-admit-cutdown-fusion
---

Given `a in A_+` and `epsilon>0`, apply the finite-packet theorem with
`epsilon/2`.  It gives square-zero `x_1,...,x_n` for which

```text
h=(a-epsilon/2)_+ in I=Ideal(x_1)+...+Ideal(x_n).
```

Apply finite cutdown fusion to this `h` with `delta=epsilon/2`.  The resulting
square-zero element `x` satisfies

```text
(a-epsilon)_+=(h-epsilon/2)_+ in Ideal(x),
```

which is exactly the conclusion of Problem LXXIII.
