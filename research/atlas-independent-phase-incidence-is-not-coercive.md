---
rg: 2
id: atlas-independent-phase-incidence-is-not-coercive
kind: claim
title: The twenty-seven Atlas phase edges have an exact private-edge escape before orbit coupling
distinct_from:
  atlas-five-row-operator-phase-lift: that asks for coercivity on the special orbit P_x=lambda(x)Ulambda(x)^* of one common chart unitary; this proves that the corresponding inequality is false when the finitely many phase vertices are treated as independent unitaries.
  atlas-linear-energy-controlled-by-full-packet-defect: that uses all 234 boundary rows and one common chart unitary; this isolates the six-cycle incidence complex of the five-row reduction and shows incidence alone supplies no reverse telescope.
---

Let `G=A_8`, let `lambda` be its left regular representation, and give an
independent unitary variable `P_x` to every prefix vertex occurring in the
five selected boundary words

```text
0, 11, 30, 44, 55
```

or in the interior word `c_19243`.  If the ordered chart-two prefix edges of
a word `w` are `(u_i,v_i)`, put

```text
H_w(P)=(product_i P_(u_i) P_(v_i)^*) lambda(fold(w)),
L_w(P)=sum_i (P_(u_i)-P_(v_i)).                       (IPF1)
```

The five boundary folds are the identity.  The edge counts are respectively

```text
3,4,4,4,4,
```

and the interior word has eight edges, for twenty-seven phase-edge
occurrences in total.

There is an exact assignment in dimension `|A_8|=20160` such that

```text
H_0=H_11=H_30=H_44=H_55=H_int=I,
||L_11||_2=4.                                         (IPF2)
```

Consequently there is no finite constant `C` for the independent-phase
inequality

```text
sum_j ||L_j(P)||_2^2
 <= C [sum_j ||H_j(P)-I||_2^2+||H_int(P)-I||_2^2].    (IPF3)
```

In particular, neither the six cycle incidences nor a generic
noncommutative cycle Poincare/SOS argument can prove
`atlas-five-row-operator-phase-lift`.  Any valid proof of that claim must use
the identities

```text
P_x=lambda(x) U lambda(x)^*
```

for one common unitary `U`; those orbit identities are deliberately absent
from `(IPF3)`.
