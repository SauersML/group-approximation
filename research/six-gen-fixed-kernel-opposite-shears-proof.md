---
rg: 2
id: six-gen-fixed-kernel-opposite-shears-proof
kind: route
title: Split off one transverse hyperbolic plane and shear inside the fixed block
target: six-generator-fixed-kernel-rank-jump-admits-opposite-shears
requires: []
---

The three summands in `(SFK1)` have disjoint supports, so the four ranks in
`(SFK2)` are immediate.  Each matrix in `(SFK3)` is the identity outside
`span(e_0,e_1)` and has determinant one on that plane.  It therefore preserves
`e_0 wedge e_1`, fixes `e_2 wedge e_3`, and fixes `K`; hence it preserves the
whole form pencil coefficientwise over `F_2[x]`.

Their product restricts on the first plane to

```text
[[1+x^2,x],[x,1]].
```

The leading-monomial induction in
`cyclic-phase-pauli-shears-have-unbounded-clock-order-proof` shows strict
degree growth.  The artifact independently enumerates the entire stated
rank-four search space, checks preservation coefficient by coefficient, and
reports the minimum-weight witness.
