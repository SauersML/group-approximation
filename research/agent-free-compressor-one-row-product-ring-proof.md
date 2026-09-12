---
rg: 2
id: agent-free-compressor-one-row-product-ring-proof
kind: route
title: Use regular representations of finite product-ring elementary groups
target: agent-free-compressor-one-row-product-ring-no-go
requires: []
---

Because free groups are torsion-free and residually finite, the orders of the
image of `r` in finite quotients are unbounded.  Indeed, if every such order
were at most `m`, then `r^(lcm(1,...,m))` would vanish in every finite quotient,
contrary to residual finiteness.  Choose quotients

```text
q_n:F->Q_n,              ell_n=ord(q_n(r))->infinity. (OPF1)
```

The ring maps

```text
R -> R_n=F_p times F_p[Q_n]                           (OPF2)
```

preserve `(ORP1)--(ORP2)`.  Pass from the rank-five Steinberg presentation to
its finite elementary quotient

```text
G_n=E_5(R_n)=E_5(F_p) times E_5(F_p[Q_n])             (OPF3)
```

and take the left regular unitary representation of `G_n`.  This is an exact
finite matrix representation of every root and commutator row in question.

The element `Z_n=x_13((1,0))` lies entirely in the first factor of `(OPF3)`
and has order `p`.  Left translation by an element of order `p` has each
`p`-th root of unity with equal multiplicity.  Therefore

```text
tr(1-P_(Z_n,1))=1-1/p.                                (OPF4)
```

The diagonal element `D_(r,n)` lies entirely in the second factor.  The basis
unit `q_n(r) in F_p[Q_n]` has order `ell_n`, hence so does

```text
diag(q_n(r),q_n(r)^(-1),1,1,1).
```

Left translation by `D_(r,n)` consequently has the uniform spectral measure
on the `ell_n`-th roots of unity.

For `delta>0`, spectral calculus gives for every projection `e_n`

```text
tr(e_n)
 <= #{z^ell_n=1: |z-1|<=delta}/ell_n
    +delta^(-2)||(D_(r,n)-1)e_n||_2^2.                (OPF5)
```

The first term has limsup at most the normalized arc length of
`{z in T:|z-1|<=delta}`, which tends to zero with `delta`.  Under `(ORP5)`,
first let `n->infinity` in `(OPF5)` and then `delta->0`; this proves `(ORP6)`.

Finally, the two elements lie in different direct factors of `(OPF3)`, so
they commute exactly.  More strongly, the ring equality `(u_r-1)P=0` already
holds before passage to the elementary group, and hence every Steinberg root
word used to encode that equality is exactly trivial.  Equations
`(OPF4)--(OPF5)` therefore contradict `(ORP7)` at zero presentation defect,
completing the fixed-row no-go.
