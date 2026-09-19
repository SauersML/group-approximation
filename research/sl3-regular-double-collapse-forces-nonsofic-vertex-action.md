---
rg: 2
id: sl3-regular-double-collapse-forces-nonsofic-vertex-action
kind: claim
title: Regular fold collapse for the SL3 arithmetic double would force nonsoficity of its 2-adic vertex action
artifacts:
  - research/artifacts/sl3-arithmetic-double-regular-trace-firewall-2026-08-21.md
distinct_from:
  sofic-dyadic-action-produces-full-hnn-iwahori-countermodels: that treats the rank-one Iwahori/HNN transfer failure; this applies the same generalized-free-wreath mechanism to the rank-two arithmetic double and its fold word.
  sl3-regular-arithmetic-double-fold-mark-collapse: that is the desired matrix collapse; this theorem records a necessary dynamical consequence and an exact conditional sofic countermodel.
---

Let `X=A/C` for

```text
A=SL_3(Z[1/2]),       C=SL_3(Z).
```

If the action `A curvearrowright X` is sofic, then the free generalized
wreath product

```text
H=( *_(x in X) Z_x ) rtimes A
  = <A,t | [t,C]=1>
```

is sofic by Gao--Kunnawalkam Elayavalli--Patchell.  The adjacent vertex
subgroup `<A,tAt^(-1)>` is `D=A *_C A`, hence `D` is sofic.  Its canonical
permutation microstates have regular character and, for the nontrivial fold
word

```text
w=i_0(h)i_1(h)^(-1),
```

satisfy

```text
||sigma_n(w)-I||_2 -> sqrt(2),                            (SVA1)
```

not zero.  Therefore soficity of the vertex action explicitly refutes
`sl3-regular-arithmetic-double-fold-mark-collapse`; that collapse would prove
the action nonsofic.

The coset space is the type-zero vertex orbit of the `2`-adic affine
building: `C=A intersect SL_3(Z_2)`, density of `A` in `SL_3(Q_2)` gives
`A/C=SL_3(Q_2)/SL_3(Z_2)`.  Existing positive action-soficity criteria do not
settle it because the stabilizer `C` is nonamenable and not locally finite,
while finite quotient actions collapse by co-density.

