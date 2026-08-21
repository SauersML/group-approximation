---
rg: 2
id: full-weyl-defect-pvm-parseval-proof
kind: route
title: Fourier-expand conjugation and apply operator-valued Parseval
target: full-weyl-defect-equals-pvm-transport-energy
requires:
  - expander-pvm-transport-forces-dimension-or-mass-collapse
---

Write

```text
U(a)=sum_x (-1)^<a,x> P_x.
```

For fixed `b`, reindexing `x` by `x+b` gives

```text
Delta(a,b)
 =sum_x (-1)^<a,x> (W(b)P_xW(b)^*-P_(x+b)).                  (1)
```

The characters of `V` are orthonormal for the uniform measure.  Parseval in
the Hilbert space `L^2(M_d,tr_d)` therefore gives

```text
E_a ||Delta(a,b)||_2^2
 =sum_x ||W(b)P_xW(b)^*-P_(x+b)||_2^2.                        (2)
```

Average `(2)` over `b` to obtain `(FWD2)`.  The Markov operator of the
complete translation graph is

```text
Mf(x)=E_b f(x+b)=E_y f(y),
```

so it vanishes on mean-zero functions and has gap one.  Apply `(EP2)` with
`N=2^n` to get `(FWD3)--(FWD4)`.
