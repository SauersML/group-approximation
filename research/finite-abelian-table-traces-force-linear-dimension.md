---
rg: 2
id: finite-abelian-table-traces-force-linear-dimension
kind: claim
title: Approximate finite abelian tables with small traces force dimension proportional to the group order
distinct_from:
  all-abelian-uniform-hs-rounding-gives-global-pvm: That gives same-dimension exactification with a group-independent modulus; this proves an explicit dimension lower bound directly from aggregate Fourier errors, without constructing a simultaneous PVM.
  leavitt-finite-trace-tests-regularize-both-factor-profiles: That corrects the two fixed native finite factors; this gives growing dimension pressure from the larger native subgroups C_3^r.
artifacts:
  - research/artifacts/finite-abelian-fourier-dimension-pressure-2026-09-08.md
---

Let `A` be a finite abelian group of order `m>=2`. Suppose
`sigma:A->U(n)`, `sigma(1)=I`, has complete-table normalized-HS
defect at most `epsilon`, and

```text
max_(a!=1) |tr sigma(a)|<=a_0.
```

Put `D=(11/2)*sqrt(m)*epsilon` and `x_+=max(x,0)`. Then

```text
n >= m (1-D)_+ / (sqrt(1+(m-1)*a_0^2)+D)^2.
```

At `epsilon=0` this gives `n>=m/(1+(m-1)*a_0^2)`, and in
particular exact regular traces force `n>=m`.

For every `r>=1`, there is a finite list of literal true native
relations of `H=L_(F_2)(1,2)^x` consisting of a complete table
for `C_3^r` and conjugacy rows identifying every nonidentity
table element with the native cycle `c`. If a unitary evaluation
has defect at most `epsilon` on this list, apply the displayed
bound with

```text
m=3^r,       a_0=|tr C|+epsilon.
```

In particular,

```text
|tr C|<=epsilon<=1/(32 sqrt(3^r))  ==>  n>=3^r/2.
```

The projections used in the proof are rounded individually and
need not be mutually orthogonal. Aggregate Fourier estimates
and the integrality of their ranks suffice. The packet grows
with `r`; this supplies no uniform gap for one fixed packet and
does not decide full-kernel feasibility or hyperlinearity.
