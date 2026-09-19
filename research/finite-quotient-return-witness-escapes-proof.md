---
rg: 2
id: finite-quotient-return-witness-escapes-proof
kind: route
title: Separate the return from a finite edge window before finite-image absorption
target: exact-full-actor-hides-return-beyond-fixed-edge-windows
requires:
  - kt-exact-kun-thom-edge-return-is-algebraically-absorbed
---

Let `F subset Gamma` and `S subset G\{1}` be finite.  Every element

```text
h f^(-1),       f in F,                                 (QWE1)
```

is nontrivial because `h notin Gamma`.  The explicit Kun--Thom actor `G` is
residually finite.  Taking a product of finitely many separating quotients
gives one finite quotient

```text
pi:G->Q                                                (QWE2)
```

such that

```text
pi(s)!=1                    for every s in S,
pi(h)!=pi(f)                for every f in F.           (QWE3)
```

Put `rho=lambda_Q o pi`.  The normalized character of a finite left regular
representation is the indicator of the quotient kernel, so the first line
of `(FEW3)` follows.  Moreover

```text
<rho(h),rho(f)>_2
 =tr(lambda_Q(pi(h)^(-1)pi(f)))=0                      (QWE4)
```

by `(QWE3)`.

On the other hand `rho` is an exact finite-dimensional representation of
the complete actor.  The established exact-return absorption theorem gives

```text
rho(h) in C*(rho(Gamma)).                               (QWE5)
```

In this regular quotient model the group elements form a basis of the finite
group algebra.  Hence `(QWE5)` says precisely that `pi(h)` belongs to
`pi(Gamma)`: choose `gamma_(F,S) in Gamma` with
`pi(gamma_(F,S))=pi(h)`.  Equation `(QWE3)` forces this witness outside `F`,
proving `(FEW5)`.

Finally choose increasing finite sets `S_n` exhausting `G\{1}` and `F_n`
exhausting `Gamma`, and apply the construction at each `n`.  Every fixed
nonidentity actor word eventually belongs to `S_n`, so the regular quotient
characters converge pointwise to the canonical character.  Equations
`(QWE4)--(QWE5)` hold at every stage.  The return absorption witness therefore
moves beyond every fixed edge radius while all actor equations remain exact.
