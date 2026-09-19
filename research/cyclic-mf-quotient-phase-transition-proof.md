---
rg: 2
id: cyclic-mf-quotient-phase-transition-proof
kind: route
title: Specialize camouflage closure to a group all of whose quotients are MF
target: cyclic-mf-quotient-phase-transition
requires:
  - mf-semantic-closure-transplantation
  - compression-defect-dies-in-finite-dimensions
---

Use the finitely presented Hilbert-hotel seed `(B,d)` in camouflage surgery
and take `Q=Z`.  Every quotient of `Z` is cyclic and hence MF.  Formula `(S1)`
therefore gives, for every normal `N`,

```text
cl_MF^W(N)=pi^(-1)(pi(N))=N ker(pi)
          =N normalClosure(d).
```

The quotient criterion follows immediately.  At `N={1}` it says that `W`
is non-MF and has exact radical `normalClosure(d)`, while killing `d` leaves
`Z`.  Finite presentability follows from finite presentability of the two
vertices and cyclicity of the amalgamated subgroup.

The same compression defect is killed in every finite-dimensional linear
representation of `B` over every field and normally generates `B`.  Hence
every such representation of `B` is trivial, and the amalgam factorization
proof applies verbatim to every `GL_n(F)`.  It then applies to finite and
residually finite targets.  Peter--Weyl point separation extends it to
compact targets and therefore to maximally almost periodic and profinite
targets.  The universal properties of Bohr and profinite completion give the
claimed canonical identifications.
