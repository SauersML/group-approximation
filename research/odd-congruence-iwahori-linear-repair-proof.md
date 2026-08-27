---
rg: 2
id: odd-congruence-iwahori-linear-repair-proof
kind: route
title: Use Selberg averaging and odd-level edge fullness to repair the whole vertices
target: odd-congruence-iwahori-pairs-have-uniform-linear-repair
requires: []
---

Put `rho(b)=pi_+(b)` and `eta(b)=pi_-(sigma(b))`.  On normalized
Hilbert--Schmidt matrices consider the left-right representation

```text
beta(b)T=rho(b)T eta(b)^*.                                (OLP1)
```

Because both vertex representations have odd congruence level, `beta`
factors through an odd congruence quotient of `B_+`.  Selberg property
`(tau)`, inherited by the fixed finite-index subgroup `B_+`, gives a
constant `kappa>0`, independent of both levels and `d`, such that the
orthogonal projection `E` onto `Fix(beta)` obeys

```text
A=E(I),                 ||A-I||_2<=epsilon/kappa=:delta. (OLP2)
```

The fixed-vector equation says that `A eta(b)=rho(b)A`.  Write
`A=U|A|`, with initial and final support projections `p=U^*U` and
`q=UU^*`.  Then

```text
p in eta(B_+)',         q in rho(B_+)',
U eta(b)p=rho(b)U,      tr(1-p)=tr(1-q)<=delta^2.       (OLP3)
```

The last inequality follows because `A` vanishes on `1-p`, whereas the
identity has singular value one there.

Here is the arithmetic step that is unavailable for general edge types.
For every odd `m`, the image of either Iwahori subgroup in
`SL_2(Z/m)` is the whole group.  Indeed, in projective coordinates the
edge generators contain

```text
u=[[1,1],[0,1]],        u^(-1)e=[[-1,0],[2,-1]],       (OLP4)
```

so their reductions contain the upper elementary generator and, because
`2` is invertible modulo `m`, the lower elementary generator; these
generate `SL_2(Z/m)` (with the central generator retained in the `SL_2`
version).  Equivalently, the principal level-two subgroup contained in the
Iwahori subgroup surjects at every odd level.  Consequently `p` reduces the
whole second vertex representation and `q` reduces the whole first vertex
representation, not merely their edge restrictions.

Complete the polar partial isometry to a unitary `V=U+W`, where `W` maps
`(1-p)C^d` onto `(1-q)C^d`.  It may be chosen with

```text
||V-I||_2<=4 delta.                                    (OLP5)
```

For completeness, Mirsky's singular-value inequality gives
`||U-A||_2<=delta` on `p`, hence `||(U-I)p||_2<=2delta`; the arbitrary
completion contributes at most `2 sqrt(tr(1-p))<=2delta`.

Now replace each vertex action on its small reducing complement by the
trivial representation:

```text
pi~_+(g)=q pi_+(g)q+(1-q),
pi~_-(h)=V (p pi_-(h)p+(1-p)) V^*.                    (OLP6)
```

These are exact representations.  On the large supports, `(OLP3)` gives
the edge equality; on the complements both actions are trivial.  Hence
`(OLP6)` satisfies `(OCR2)`.  For every vertex generator,

```text
||pi_+(g)-pi~_+(g)||_2<=2delta,
||pi_-(h)-pi~_-(h)||_2<=2delta+2||V-I||_2<=10delta.   (OLP7)
```

Combining `(OLP2)` and `(OLP7)` proves `(OCR3)` with `K=10/kappa`.

