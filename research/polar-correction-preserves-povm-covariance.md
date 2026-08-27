---
rg: 2
id: polar-correction-preserves-povm-covariance
kind: claim
title: Polar correction preserves one POVM covariance row with a fixed spectral gap
---

**ESTABLISHED.**  Let `P` be a projection in a finite tracial matrix
algebra.  Let `Y=YP` be a contraction satisfying

```text
H=Y^*Y>=lambda P                    (lambda>0),        (PCV1)
```

and let

```text
S=YH^(-1/2),
B_P=PBP.                                                (PCV2)
```

Here the inverse is taken in `PMP`.  For self-adjoint unitaries `A,B`, put

```text
epsilon=||AY-YB||_2.                                   (PCV3)
```

Then `S^*S=P` and

```text
||AS-SB_P||_2
 <=(lambda^(-1/2)+lambda^(-3/2)) epsilon.              (PCV4)
```

The full covariance row used by the POVM game decoder satisfies

```text
||AS-SB||_2
 <=(2lambda^(-1/2)+lambda^(-3/2)) epsilon.             (PCV5)
```

No assumption that `P` commutes with `B`, or that `SS^*` commutes with `A`,
is used.  The compressed contraction `B_P` is exactly the observable of the
binary Bob POVM in
`common-source-partial-isometries-decode-one-game-state`.

For the sequential carrier of
`sequential-overlap-polar-aligns-carriers-not-contexts`, one has
`lambda=a/2`.  Hence ordinary-word control of the raw prefix covariance

```text
||A_(c,x)Y_c-Y_cB_x||_2                               (PCV6)
```

passes to the polar common-source strategy with a constant depending only
on the fixed profile overlap `a`, never on matrix dimension.
