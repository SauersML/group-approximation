---
rg: 2
id: stw63-type1-cardinal-rank-collapse-proof
kind: route
title: Fullness forces full Hilbert cardinal rank and Hadwin classifies the representations
target: stw63-arbitrary-type1-factor-uniqueness
requires: []
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

The precise imported result is Hadwin, *Nonseparable approximate
equivalence*, Transactions AMS 266 (1981), Theorem 2.5: for a C-star algebra
`A`, an arbitrary Hilbert space `H`, and nondegenerate representations
`rho,sigma:A->B(H)`, norm approximate unitary equivalence is equivalent to

```text
rank(rho(a))=rank(sigma(a))                 (a in A),        (1)
```

where rank is the Hilbert-space dimension of the closure of the range.  This
unrestricted formulation is also stated explicitly in the introduction of
Hua--White.

Suppose an embedding exists, so `H` is infinite-dimensional; write
`kappa=dim(H)`.  Fix `0!=a in Z`, and let `p` be the range projection of
`phi(a)`, with `lambda=dim(pH)`.  Fullness of `a*a` in the simple unital
algebra `Z` gives a finite `n` with

```text
1_Z <=_Cu (a*a) directSum ... directSum (a*a)   (n copies).
```

After applying `phi` and passing to range projections, `H` embeds isometrically
into `(pH)^n`.  Hence

```text
kappa <= n lambda <= n kappa.                                (2)
```

The first inequality rules out finite `lambda`.  Infinite-cardinal arithmetic
then gives `n lambda=lambda`, while `pH subset H` gives `lambda<=kappa`.
Thus (2) forces `lambda=kappa`.  The same proof applies to `psi(a)`; the zero
element has rank zero.  Consequently (1) holds on all of `Z`, and Hadwin's
theorem supplies the required unitaries.
