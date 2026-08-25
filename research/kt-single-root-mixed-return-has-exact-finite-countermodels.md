---
rg: 2
id: kt-single-root-mixed-return-has-exact-finite-countermodels
kind: claim
title: One root-stabilizer correlation does not charge the Kun--Thom marked return
distinct_from:
  kt-ab-marked-return-is-the-first-mixed-cylinder: That identifies the first mixed return and the terminal marked pair; this proves that imposing only its one visible root-stabilizer row still has exact finite models retaining the pair.
  kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath: That constructs models on the external SL3 orbit without any Gamma root; this countermodel includes the mixed root r, its conjugate h, and every actor relation.
  two-site-a5-center-has-exact-boundary-countermodel: That is a representation-theoretic boundary model for an abstract two-site packet; this is an arithmetic finite quotient of the pinned Kun--Thom actor and its binary coset wreath.
---

**ESTABLISHED.**  Let

```text
r=e_12(x_1),   h=LrL^(-1)=e_12((x_1x_2x_3)^(-1))
```

be the explicit mixed return of `kt-ab-marked-return-is-the-first-mixed-cylinder`.
For every finite actor window there is an exact finite-dimensional unitary
model satisfying all actor relations, the base-lamp involution relation, the
single stabilizer row `[a,r]=1`, and `b=hah^(-1)`, in which

```text
||(1+a)/2-(1+b)/2||_2^2=1/2.                         (KSR1)
```

The chosen finite actor window can simultaneously have its canonical regular
trace.  Thus no normalized-HS estimate using only the actor relators, this one
root-stabilizer correlation, and the two displayed lamp covariance rows can
force the marked pair to coalesce or force an actor-normalized diagonal.  A
positive transfer must use a finite family of Gamma-stabilizer rows (and their
joint interaction with the lamp table), not merely the root which occurs in
the word for `h`.

DERIVATION
kt-single-root-mixed-return-finite-countermodel-proof
