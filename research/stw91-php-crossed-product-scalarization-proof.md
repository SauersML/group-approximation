---
rg: 2
id: stw91-php-crossed-product-scalarization-proof
kind: route
title: Scalarize the PHP crossed-product expectation and apply tracial selfless regularity
target: stw91-php-approximately-inner-crossed-products-are-selfless
requires:
  - gjkepr-php-crossed-product-expectations-are-selfless
  - gjkepr-simple-unique-trace-bases-scalarize-selfless-expectations
  - robert-tracial-selfless-regularity
artifacts:
  - research/artifacts/stw91-php-crossed-product-selflessness-audit-2026-08-30.md
---

Write `A=B rtimes_(alpha,r) G`.  By
`gjkepr-php-crossed-product-expectations-are-selfless`, the PHP and
approximate-innerness hypotheses make `(A,E,B)` a selfless operator-valued
C*-probability space.

Since `B` is simple with unique tracial state `tau`,
`gjkepr-simple-unique-trace-bases-scalarize-selfless-expectations` applies
and makes `(A,tau compose E)` selfless.  Faithfulness is automatic: the
canonical reduced-crossed-product expectation is faithful and `tau` is
faithful because `B` is simple.  The state is tracial: uniqueness of `tau`
gives `tau compose alpha_g=tau` for every `g`, and on algebraic
crossed-product monomials

```text
(tau compose E)((b u_g)(c u_h))
  = 0                              if gh != e,
  = tau(b alpha_g(c))              if h = g^(-1),
```

which is unchanged when the two monomials are reversed, using traciality
and `alpha_g`-invariance of `tau`.  Density gives the trace identity on all
of `A`.

Now `robert-tracial-selfless-regularity` supplies simplicity, stable rank
one, strict comparison, and uniqueness of both the tracial state and the
normalized 2-quasitrace.

For `B=Z`, Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert explicitly
record after Theorem 1.4 that every automorphism of `Z` is approximately
inner.  Thus every action satisfies the action hypothesis, and the general
argument applies without any outerness or Rokhlin-type assumption.
