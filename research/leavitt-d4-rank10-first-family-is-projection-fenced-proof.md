---
rg: 2
id: leavitt-d4-rank10-first-family-is-projection-fenced-proof
kind: route
title: Reduce the first rank-ten family to four conjugate projections
target: leavitt-d4-rank10-first-family-is-projection-fenced
requires:
  - leavitt-d4-length12-rank10-has-15-cyclic-classes
---

The representative has carrier equations

```text
H A0=E5^-1 H E4^-1 H,
H^-1C0=A1^-1H^-1,
H^-1C1=E1^-1H^-1,
```

and boundary `K=H^-1B0 H^-1B1 H^-1E2 H E3`.  The common middle equation
has branches I and II from the rank-nine analysis.  The third equation gives
`ep=1`; branch II additionally has `z=1` and is the `v=1` subcase of branch I.
Thus `H=c0d1a2b3`, and the remaining carrier equation is

```text
c0 d1 a2 (bpa b^-1)3 a^-1_2 d^-1_1 (c^-1v^-1u^-1)0
a1 b2 (c b^-1)3 a^-1_2 d^-1_1 (c^-1du)0 = 1.       (R10)
```

One minimal cancellation scheme in `(R10)` gives

```text
b=a=d, u=d^-1, c=v^-1d, p=d^-1v, e=c.
```

Writing `D=d^-1,V=v^-1`, the exact boundary has syllables

```text
D3 D2 D1 (Dvd)0 (Vd)1 d2 V3 D2 D1 (Dvd)0
d1 V2 D1 (Dvd)0 d1 d2 d3.
```

Its four copy projections reduce to

```text
K0=d^-1v^3d,       K1=K2=K3=d^-1vd.
```

If three projections are trivial then `v=1`, hence `K0=1`.  This family is
therefore globally fenced without any coefficient-library assumption.
