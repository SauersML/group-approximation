---
rg: 2
id: property-t-free-torsion-free-via-bs-radical-tether
kind: route
title: Tether one torsion-free radical word, route it, and saturate the quotient
target: property-t-free-torsion-free-full-mf-radical
requires:
  - property-t-free-torsion-free-fp-non-mf-seed
  - universal-mf-quotient
  - baumslag-solitar-radical-tether-preserves-mf-reflection
  - internal-torsion-free-single-word-router
  - torsion-free-mf-radical-routing-saturation
---

Choose the torsion-free finitely presented non-MF group `E`.  By
`universal-mf-quotient`, choose

```text
1 != d in Rad_MF(E).
```

Form the Baumslag--Solitar tether

```text
A=<E,t | d t d^(-1)=t^2>.
```

The tether theorem says that `A` is finitely presented, torsion-free and
acylindrically hyperbolic, that `E` embeds in `A`, and that
`d in Rad_MF(A)` remains nontrivial.  Apply
`internal-torsion-free-single-word-router` to `(A,d)`, protecting `d`.  It
gives a surjection `q:A->>Q` with `q(d)!=1`, `<<q(d)>>^Q=Q`, and `Q`
two-generated, finitely presented, torsion-free and acylindrically
hyperbolic.

Finally `torsion-free-mf-radical-routing-saturation` gives
`Rad_MF(Q)=Q` and the same conclusion for every nontrivial quotient of `Q`.
The construction uses no Property `(T)` or Kazhdan input.  Consequently the
analytic content of the torsion-free manuscript endpoint is exactly the
minimal seed claim; all remaining adjectives are algebraic/geometric
promotion steps.
