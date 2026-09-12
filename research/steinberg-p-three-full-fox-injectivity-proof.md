---
rg: 2
id: steinberg-p-three-full-fox-injectivity-proof
kind: route
title: Eliminate the nine characteristic-three chord fibers
target: steinberg-flag-fox-map-is-injective-at-p-three
requires:
  - steinberg-y-anchor-leaves-one-boundary-mode
  - steinberg-fox-chord-actions-are-explicit
  - steinberg-tree-cuts-are-five-marginals
---

Work in `F_3`, where `eta=1/2=2`.  Write

```text
F_ab(c)=f(a,b,c),
mathcalA(a)=sum_(b,c)F_ab(c),
```

and list each fiber in the order `c=0,1,2`.  The exceptional `Y` anchor
`(SYB1)` gives

```text
F_20=(0,kappa,kappa),             P(2,0)=-kappa.       (SPFI1)
```

**First adjacent fiber.**  Evaluate `X` at `(2,0,c)`.  Since `a=2=eta`,
the `A`-tree difference cancels.  At `c=0` the equation is
`-F_21(2)=0`; at `c=2` it is
`kappa-F_21(1)-kappa=0`.  At the `c=1` `B` exception it is

```text
-P(2,0)+P(2,1)-kappa=0.
```

Thus

```text
F_21=0.                                                (SPFI2)
```

**The `b=1` pair.**  Put `U=F_11`, `V=F_01`,

```text
delta=mathcalA(1)-mathcalA(0),
K=H(2,0)-H(2,1),       K'=H(1,2)-H(1,1).
```

Direct use of `(SCA4)` and `(STM2)` gives

```text
Y(1,1,*):
 U0+V0+delta=0,
 U1-V1+delta+P(0,1)=0,
 U2+V2+delta=0;

Y(0,1,*):
 -V0-U0-K=0,
 V1+V2+P(1,1)-K=0,
 V2+V1-U2-K=0;

Y(2,1,c):
 -U(c)-K'+U(2c)=0.                                  (SPFI3)
```

The `c=1` value in the last row is its `r`-tree value and uses
`P(2,1)=0`.  Solving `(SPFI3)` first gives `K'=0`,
`U=(0,u,u)`, `P(1,1)=-u`, and then

```text
V=(-delta,delta-u,-u),       K=delta,       P(0,1)=u.
```

The `c=2` equation in the first row gives `delta=0`.  Hence

```text
U=(0,u,u),                   V=(0,-u,-u).              (SPFI4)
```

**The `b=2` fibers.**  Put `W=F_22`.  The three values of `X(0,1,c)`
give

```text
W=(kappa+u,0,kappa),         P(2,2)=u-kappa.           (SPFI5)
```

Put `J=F_12`.  The values of `X(1,2,c)`, including the `c=1` tree
exception, give

```text
J=(-u-kappa,u-kappa,-u),     P(1,2)=kappa-u.           (SPFI6)
```

Finally put `N=F_02`.  The ordinary values `c=0,2` of `Y(1,2,c)` and its
`c=1` `r`-tree value give

```text
N=(kappa+u,kappa+u,u),       P(0,2)=-kappa.            (SPFI7)
```

Now the `u`- and `r`-tree values in `Y(2,2,1)` reduce to

```text
W1-J1+P(0,1)+J2+P(0,2)=-u=0.                          (SPFI8)
```

Thus `u=0`.  Equations `(SPFI4)--(SPFI7)` become

```text
U=V=0,
W=(kappa,0,kappa),
J=(-kappa,-kappa,0),
N=(kappa,kappa,0).                                   (SPFI9)
```

Evaluate `Y` at `(0,2,2)`.  Its `q`-difference is `N2-W2=-kappa`.
The `u` denominator vanishes, but the two point cuts are `-P(2,1)` and
`-P(1,1)`, both zero.  The scaled `r`-difference is
`N1-W2=kappa-kappa=0`.  Hence

```text
kappa=0.                                              (SPFI10)
```

**The last two fibers.**  Seven of the nine fibers are now zero.  Let
`L=F_10` and `M=F_00`.  The ordinary values `X(1,0,0)` and `X(1,0,2)`
give `L0=L1=0`; the `c=1` `B` exception is

```text
-L2-P(1,0)-L1=0,
```

so `L=0`.  Next `X(0,0,0)` gives `M0=M2`, and `X(0,0,2)` gives
`M2=M1`.  Thus `M(c)=m` is constant.  In characteristic three
`P(0,0)=3m=0`, and direct substitution in the plane marginal gives

```text
H(c,d)=m if d=0, and 0 otherwise.                     (SPFI11)
```

At `(2,1,0)`, the last `X` equation consists of the `A`-tree difference
and three already-zero chord values:

```text
-H(2,2)+H(2,0)+F_12(0)-F_11(2)-F_21(0)=m=0.          (SPFI12)
```

Therefore every fiber is zero.  All exceptional substitutions above are
exactly the point and plane cuts in `(STM2)`; no zero-marginal identity
was used.
