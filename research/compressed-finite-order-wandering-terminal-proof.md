---
rg: 2
id: compressed-finite-order-wandering-terminal-proof
kind: route
title: Telescope the almost reducing compression and use faithfulness of the regular trace
target: compressed-finite-order-wandering-is-terminal
requires: []
---

Write `Q=q_U`, `W=w(U)`, `A=QWQ`, and

```text
epsilon=||A-V_U||_2.
```

All norms below are normalized Hilbert--Schmidt norms.  Since `W` is unitary
and `V_U` is unitary in the `Q` corner,

```text
||(1-Q)WQ||_2^2
 =tr(Q)-||QWQ||_2^2
 <=epsilon(||V_U||_2+||QWQ||_2)
 <=2 epsilon.                                          (CFP1)
```

The orthogonal `Q` and `1-Q` rows therefore give

```text
||WQ-V_U||_2^2
 =||QWQ-V_U||_2^2+||(1-Q)WQ||_2^2
 <=epsilon^2+2epsilon.                                 (CFP2)
```

(The transpose convention `QW-V_U` is identical, using the equality of the
two off-diagonal Hilbert--Schmidt block norms of a square unitary.)  Put
`eta=(epsilon^2+2epsilon)^(1/2)`.  Telescoping one factor at a time and using
unitary invariance gives, for every fixed `k`,

```text
||W^k Q-V_U^k||_2 <= k eta.                            (CFP3)
```

For `k=m`, `(CFW1)` yields

```text
||(W^m-1)Q||_2 <= m eta ->0.                           (CFP4)
```

Fixed finite-packet exactification changes `(CFP4)` by `o(1)`, so the same
conclusion holds for the evaluation of the fixed element `(w^m-1)q` on the
original canonical microstates.

If `Gamma` were hyperlinear, canonical moment convergence would give

```text
||(w(U_n)^m-1)q(U_n)||_2
   ->||(w^m-1)q||_(2,L(Gamma)).                        (CFP5)
```

The right side is positive.  Indeed, if `(w^m-1)q=0`, then
`w^m supp(q)=supp(q)` with coefficients preserved.  Left multiplication by
`w^m` is a permutation of this nonempty finite set.  Some positive power is
therefore the identity on a support element, and cancellation gives
`w^(mN)=1` for some `N>0`, contradicting the infinite order of `w`.
Faithfulness of the canonical trace now makes `(CFP5)` positive, whereas
`(CFP4)` makes it zero.  This contradiction proves the claim.

