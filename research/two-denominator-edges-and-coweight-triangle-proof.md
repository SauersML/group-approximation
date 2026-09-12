---
rg: 2
id: two-denominator-edges-and-coweight-triangle-proof
kind: route
title: Reduce the two coweight directions away from p and telescope the odd triangle
target: two-denominator-edges-retain-the-exact-two-sheet-atlas
requires: []
---

Let `Q_m=SL_3(Z/mZ)` and let `q_m:Lambda->Q_m` be reduction, where
`gcd(m,p)=1`.  Each `d_r` in `(DTA1)` has a reduction `dbar_r in Q_m`.
Write

```text
alpha_r=Ad(dbar_r) in Aut(Q_m).                          (CTP1)
```

For the two-edge presentation `(DTA3)`, define

```text
lambda.(x,j)=(q_m(lambda)x,j),
s.(x,j)=(alpha_12(x),j+1),
t.(x,j)=(alpha_23(x),j+1).                              (CTP2)
```

If `c in I_r`, then

```text
alpha_r(q_m(c))=q_m(d_r c d_r^(-1))=q_m(phi_r(c)),      (CTP3)
```

so the two overlap-conjugacy tables hold exactly.  Since `d_12` and `d_23`
commute, `alpha_12` and `alpha_23` commute; the two sheet flips also commute.
Thus `[s,t]=1`, proving that `(CTP2)` is an exact action of `(DTA3)`.  Both
letters reverse `ell(x,j)=j` everywhere.

The same formula may be used for `d_31`.  It still satisfies its overlap
table and commutes with the first two letters.  But `(CTA2)` makes the
product of the three `Q_m`-coordinate automorphisms the identity while the
product of three sheet flips is one sheet flip.  Hence the triangle relator
fails at every point.  This identifies the first missing relation exactly.

For the quantitative statement, follow the triangle in the order

```text
omega -> d_31 omega -> d_23 d_31 omega
      -> d_12 d_23 d_31 omega=omega.                    (CTP4)
```

Three successful flips would change `ell` an odd number of times and could
not return to its initial value.  Therefore, for every `omega`, at least one
of the following occurs:

```text
ell(d_31 omega)=ell(omega),
ell(d_23 d_31 omega)=ell(d_31 omega),
ell(d_12 d_23 d_31 omega)=ell(d_23 d_31 omega).         (CTP5)
```

Take probabilities.  The action preserves the uniform measure, so the
three terms in the union bound have probabilities `delta_31`, `delta_23`,
and `delta_12`, respectively.  Their union is all of `Omega`; hence
`delta_12+delta_23+delta_31>=1`, and the maximum is at least `1/3`.
