---
rg: 2
id: steinberg-tree-cut-marginal-proof
kind: route
title: Evaluate every Steinberg spanning-tree cut by chord marginals
target: steinberg-tree-cuts-are-five-marginals
requires:
  - steinberg-cycles-have-big-cell-chord-coordinates
  - steinberg-fox-chord-actions-are-explicit
---

Orient tree edges from their point endpoint to their plane endpoint and use
the signed component formula `(SBP4)`.  Deleting an outer-point leaf collects
exactly the chords with fixed `(a,b)`, giving `-P(a,b)`.  Deleting an
outer-plane leaf fixes its normalized covector `[d:-c:1]`; the incident
chords are `(x,xc-d,c)`, giving `-H(c,d)`.  After those leaves are removed,
the `H_0` arm indexed by `c` collects `C(c)`, the `z` arm indexed by `a`
collects `A(a)`, and the central cut collects every chord with the opposite
orientation, giving `-T`.  These exhaust the double-star tree.

Consequently the individual exceptional substitutions include

```text
L_A f(1/2,b,c) = -H(2b,c/2-b),
L_B f(a,b,1)   = -P(4(a-b),2b),
L_r f(a,b,-1)  = -P(a+b,b).                           (STM3)
```

For `u`, let `e=1+ac-b+c/2`.  On `e=0,b!=1` the value is

```text
-P((a+b/2)/(1-b),b/(1-b)).                            (STM4)
```

On `b=1,a!=-1/2,c!=0` it is
`-H(t,(ac-1)/(c(a+1/2)))`, where `t=(a+1/2)^(-1)`; for the same `a` with
`c=0` it is `C(t)`.  At `b=1,a=-1/2`, it is `-T` when `c=0` and
`A(-1/2-1/c)` otherwise.  The composite exceptions are

```text
(L_A-L_Aq)f(1/2,b,c) = -H(2b,c/2-b)+H(2b,c/2),
(L_B-L_Bs)f(a,b,1)   = -P(4(a-b),2b)+P(4(a-b),2a),    (STM5)
```

and the `h^(-1)r` term is exceptional only at `c=-2`, where it equals
`-P(a/2+b/4,b/4)`.  This proves `(STM2)` and all boundary substitutions.
