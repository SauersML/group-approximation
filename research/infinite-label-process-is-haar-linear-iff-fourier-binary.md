---
rg: 2
id: infinite-label-process-is-haar-linear-iff-fourier-binary
kind: claim
title: An infinite-translate label process is Haar linear exactly when all finite Fourier moments are zero or one
distinct_from:
  finite-pmp-actions-have-barren-haar-linear-compilers: that algebraizes a finite invariant Boolean algebra by an auxiliary iid ranking factor; this characterizes when the entire infinite translate process itself already has Haar linear law.
  haar-algebraic-actions-have-permutation-koopman-spectrum: that derives spectral consequences after Haar algebraicity is known; this is an if-and-only-if test on a proposed measurable recoding and includes the multiplicative Fourier structure.
  algebraic-compact-action-envelope-for-non-ce-relation: that asks for a non-CE algebraic crossed product; this proves that a generating recoding satisfying the test is not a preliminary approximation but the desired compiler itself.
---

Let a countable group `H` act p.m.p. on a standard probability space
`(X,mu)`.  Fix a prime `p`, a finite or countable label set `I`, and measurable
functions

```text
f_i:X -> F_p,                    i in I.
```

Let `Phi:X -> (F_p^I)^H` be the equivariant name map

```text
Phi(x)(h,i)=f_i(h^(-1)x),
```

and let `nu=Phi_*mu`.  For every finitely supported coefficient array
`a in F_p^(H x I)`, put

```text
M(a)= integral_X exp((2 pi i/p)
          sum_(h,i) a_(h,i) f_i(h^(-1)x)) dmu(x).       (FLH1)
```

Then the following are equivalent:

1. `nu` is Haar measure on a closed `H`-invariant `F_p`-linear subshift
   `K <= (F_p^I)^H`.
2. Every finite Fourier moment is binary:

```text
M(a) in {0,1}                 for every finite a.       (FLH2)
```

In this case

```text
S={a:M(a)=1}
```

is the annihilator module, `K=S^perp`, and

```text
K-hat = F_p^(H x I) / S.                               (FLH3)
```

If the translates of the `f_i` generate the probability algebra of `X`, the
name map is a measurable conjugacy mod null sets from the original action to
the Haar algebraic action on `K`.  Hence

```text
L^infinity(X) rtimes H = L((K-hat) rtimes H).           (FLH4)
```

For `H=SL_3(Z)`, a non-CE action admitting such a generating recoding directly
produces a non-hyperlinear semidirect product.  Thus `(FLH2)` is the exact
infinite-translate compiler gate.

It is also an explicit obstruction.  Any finite `a` with
`M(a) notin {0,1}` disproves Haar linearity of that recoding.  For `p=2`,
`(FLH2)` says every nonzero finite `F_2`-linear combination of translated
label bits is perfectly balanced:

```text
Pr[sum a_(h,i) f_i(h^(-1)x)=1]=1/2;                    (FLH5)
```

an a.e.-zero combination has moment one.  A finite or countable relabeling
does not evade the test; it merely changes the family of functions to which
the same finite-moment criterion applies.
