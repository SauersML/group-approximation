---
rg: 2
id: finite-tracial-cstar-transport
kind: claim
title: Kazhdan transport for norm ultraproducts of finite traced C-star algebras
root: true
distinct_from:
  kazhdan-asymptotic-commutant-transport: The established theorem treats matrix coordinates; this root asks for the correct extension to other building blocks.
  left-right-finite-coordinate-obstruction: That established successor gives a genuine sufficient coordinate class.
artifacts:
  - non_mf_groups_exist.tex
  - research/artifacts/left-right-finite-coordinate-obstruction-2026-08-19.md
---

The original proposal — all unital C-star algebras carrying faithful tracial
states — is **refuted** by the manuscript's constant-coordinate example
`A_n=C*_r(E)`.  Faithful traces provide finite coordinates, traced corners
and projection lifting, but they do not make the fixed-space comparison occur
inside a finite operator algebra.

The corrected sufficient condition is now established as
`left-right-finite-coordinate-obstruction`: for each coordinate require

```text
D_tau(A)=C*(L_a,R_b:a,b in A) <= B(L^2(A,tau))
```

to be finite.  Then the norm ultraproduct of these left-right algebras is
finite, Kazhdan transport works there, the property is inherited by the
traced corners used by the obstruction, and both the central-sign and
finite-normal arguments survive.

This gives genuine infinite-dimensional building blocks, including
commutative and faithfully traced AF/UHF algebras.  The remaining
classification question is how far the left-right-finite class can be
enlarged while retaining the comparison step.
