---
rg: 2
id: minimal-multilinear-pi-has-full-factorial-support
kind: claim
title: Every minimal multilinear matrix identity has full factorial support
distinct_from:
  symmetric-sign-packet-has-factorial-amitsur-density-loss: that computes the trace loss after the standard polynomial is packaged in a regular symmetric-group corner; this proves that no different minimal-degree multilinear identity can first sparsify its monomial support.
  raw-amitsur-permutation-sampling-has-factorial-gap-loss: that bounds bounded-query tests on the raw monomial Gram table; this is an algebraic uniqueness and coefficient-mass statement before any tester is chosen.
  rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm: that applies to every exact linear extended formulation of a normalized sum; this only classifies degree-minimal multilinear polynomial identities of a full matrix algebra.
---

ESTABLISHED.  Work over `C`, fix `n>=2`, and put

```text
m=2n,                 N=m!.
```

Let

```text
f(x_1,...,x_m)=sum_(sigma in S_m) c_sigma
                 x_(sigma(1))...x_(sigma(m))          (MFS1)
```

be a nonzero multilinear polynomial identity of `M_n(C)` of degree `m`.
The minimal-identity part of the Amitsur--Levitzki theorem says that every
such identity is a scalar multiple of the standard polynomial.  Thus there
is a nonzero `c in C` with

```text
c_sigma=c sgn(sigma)       for every sigma in S_m.    (MFS2)
```

In particular every one of the `N` permutation monomials occurs, and

```text
||c_.||_1=N|c|,            ||c_.||_2=sqrt(N)|c|.      (MFS3)
```

This coefficient statement has an exact operator normalization on the Fock
boundary used by the dimension tape.  Put

```text
w_j=x y^j x,               W_j=L_(w_j).
```

The words `w_j` form a prefix code, so the `N` product isometries

```text
W_(sigma(1))...W_(sigma(m)),       sigma in S_m,
```

have pairwise orthogonal ranges.  Consequently

```text
f(W)^*f(W)=N|c|^2 I.                                  (MFS4)
```

Normalizing this exact Fock instruction to operator norm one forces

```text
|c|=N^(-1/2),            ||c_.||_1=sqrt(N).           (MFS5)
```

Therefore the degree-minimal multilinear PI route has no sparse substitute:
after the normalization which keeps the infinite instruction bounded, its
ordinary coefficientwise word telescope still carries the divergent factor
`sqrt((2n)!)`.  Reordering, rescaling, or choosing another degree-`2n`
multilinear identity cannot improve that factor.

The scope is deliberately sharp.  This does not exclude a higher-degree
sparse identity, a nonlinear/discrete redundant proof, or a delocalized
terminal observable whose estimate is not obtained by coefficientwise
telescoping.

## Source

The uniqueness input is the minimal-identity theorem of S. A. Amitsur and
J. Levitzki, *Minimal identities for algebras*, Proceedings of the American
Mathematical Society **1** (1950), 449--463,
doi:10.1090/S0002-9939-1950-0036751-9.

