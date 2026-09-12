---
rg: 2
id: two-field-matching-sampler-proof
kind: route
title: Polarize two field matchings and kill the residual alternating form
target: two-field-matchings-rigidify-linear-weyl-mislabels
requires: []
---

Use the trace pairing on `F_(2^n)`.  The identity matching makes the error
form alternating.  The `alpha` matching makes multiplication by `alpha`
self-adjoint for that form.  Since `alpha` generates the field, the form is
field-balanced and therefore has the shape `Tr(cxy)`.  Alternation plus the
bijection `x |-> x^2` gives `c=0`.

For `L!=I`, one of the two diagonal error forms is a nonzero quadratic
Boolean polynomial.  The degree-two Reed--Muller distance bound makes it
nonzero on at least one quarter of `V`, so equal sampling of the two
matchings gives a uniform rejection probability at least `1/8`.
