---
rg: 2
id: determinant-conjecture-via-integer-trace-moments
kind: route
title: Deduce the determinant bound from integrality of the trace moments of A*A
target: determinant-conjecture
requires: []
---

**Dead.** Proposed shortcut: `tau((A^*A)^j)` is an integer for every `j`, so
the spectral measure of `A^*A` has integer moments, so its log determinant is
nonnegative. The last step is false:
`integer-moment-measure-with-negative-log-determinant` gives a measure with
all moments integers and negative log determinant. Any proof must use more
than moment integrality, such as Galois equidistribution of spectral mass or
integral approximation of the whole measure.
