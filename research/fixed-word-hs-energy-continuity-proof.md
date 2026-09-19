---
rg: 2
id: fixed-word-hs-energy-continuity-proof
kind: route
title: Expand every fixed Hilbert--Schmidt energy into finitely many tracial moments
target: fixed-word-hs-energies-cannot-detect-atomic-to-diffuse-escape
requires: []
---

For fixed matrix-valued `*`-polynomials `p_i,p_j`,

```text
<p_i(U^(n)),p_j(U^(n))>_2
 =tr_n(p_i(U^(n))^*p_j(U^(n))).                        (FWE4)
```

Each matrix entry of the product on the right is a finite linear
combination of fixed `*`-words.  Tracial `*`-moment convergence therefore
gives convergence in `(FWE4)`, and taking `i=j` proves convergence of every
squared Hilbert--Schmidt norm in `(FWE1)`.

If `X=p(U)` is fixed and `mu` has finite support, then

```text
A_(mu,U^(n))(p(U^(n)))
 =sum_(g in supp(mu)) mu(g)
   U_g^(n) p(U^(n)) (U_g^(n))^*.                       (FWE5)
```

This is another fixed `*`-polynomial.  Its norm, its displacement from
`p(U^(n))`, and every inner product among finitely many such orbit vectors
are covered by `(FWE4)`.  Finite matrix amplifications merely add finitely
many entries, while finite Gram matrices and sums of squares are finite
linear combinations of the same inner products.

At every finite matrix coordinate an exact commuting finite-order root
family has a finite atomic joint spectral PVM.  Tracial moment convergence
records only the integrals of fixed character polynomials against the
associated empirical spectral measures.  Such empirical measures can
converge weakly to Haar, and then the generated limiting abelian von Neumann
algebra may be diffuse.  Minimal projections and least atom weights are not
continuous under this convergence.  Thus the coordinate atomicity supplies
no additional term in `(FWE4)--(FWE5)`.

For canonical group microstates, diagonal extraction gives tracial
`*`-moment convergence to the left regular tuple.  Substituting that tuple
in `(FWE4)--(FWE5)` proves the ordinary-Leavitt and spherical conclusions.
Any contradiction must therefore invoke extra coordinate data before the
limit, rather than ask a fixed word energy to recognize atomicity after the
fact.
