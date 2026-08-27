---
rg: 2
id: polynomial-julia-padding-cannot-flatten-spectrum
kind: claim
title: Finite polynomial Julia padding cannot flatten an arbitrary defect spectrum
distinct_from:
  shared-involution-right-ideal-interpolation-criterion: that shows a Julia or matrix dilation retains a stabilized projection CRT; this gives a scalar-spectrum obstruction to a universal finite polynomial complement.
  tight-defect-column-solves-algebraic-projection-crt: that succeeds when the original defect Gram already has one nonzero eigenvalue; this rules out manufacturing that property for arbitrary spectra by finitely many polynomial complement columns.
---

**ESTABLISHED.**  There are no finitely many complex polynomials
`f_1,...,f_m` and scalar `lambda` such that

```text
t+sum_j |f_j(t)|^2=lambda                              (FPJ1)
```

for every `t` in a nondegenerate real interval.  Consequently no universal
finite Julia/partial-isometry dilation whose added columns are polynomial
functions of an arbitrary positive defect Gram operator `K` can make

```text
K+sum_j f_j(K)^*f_j(K)=lambda I                       (FPJ2)
```

on every input spectrum.  Functional calculus can use
`(lambda-K)^(1/2)`, but no fixed finite algebraic polynomial padding can
replace it.

This obstruction concerns a universal padding formula.  It does not rule
out an input-specific algebraic spectral identity, new noncommuting
auxiliary generators, or a packet which constrains the original spectrum;
those are exactly the remaining possibilities in
`affine-frobenius-tight-defect-column-frame`.
