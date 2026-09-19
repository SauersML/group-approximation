---
rg: 2
id: a4-canonical-coherence-data-hs-lipschitz-proof
kind: route
title: Every canonical carrier is a fixed finite polynomial in the A4 generators
target: a4-canonical-coherence-data-hs-lipschitz
requires:
  - a4-line-carriers-explicit-idempotents
  - a4-regular-three-way-coherence-transducer
---

Put

```text
eps=||rho(a)-rho'(a)||_2+||rho(b)-rho'(b)||_2.
```

The order-three spectral projections are the fixed Fourier polynomials

```text
P_j=(1/3) sum_(r=0)^2 omega^(-jr) rho(a)^r,
```

so finite-word telescoping gives `||P_j-P'_j||_2<=C_1 eps`.  Likewise

```text
Q_+=(I+rho(b))/2
```

is `1/2`-Lipschitz.

By `a4-line-carriers-explicit-idempotents`, each `E_j` is the fixed twelve-term
group-algebra polynomial

```text
E_j=(1/12) sum_(g in A4) conjugate(xi_j(g)) rho(g).
```

Choose once and for all words in `a,b` for the twelve group elements.  Another
finite telescoping estimate gives

```text
||E_j-E'_j||_2<=C_2 eps,
```

with `C_2` independent of multiplicity.  Therefore the same is true for
`R_j=P_j-E_j` and

```text
S=Q_+-(E_0+E_1+E_2).
```

Finally

```text
T_j=sqrt(3) S R_j,
```

and all projections involved have operator norm at most one.  Hence

```text
||T_j-T'_j||_2
 <= sqrt(3)(||(S-S')R_j||_2+||S'(R_j-R'_j)||_2)
 <= sqrt(3)(||S-S'||_2+||R_j-R'_j||_2).
```

Combining the finitely many fixed constants proves `(A4-FAN-LIP)`.  No step
sees the external regular multiplicity.