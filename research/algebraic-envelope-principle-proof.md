---
rg: 2
id: algebraic-envelope-principle-proof
kind: route
title: Fourier duality identifies the crossed product with the group factor; CE passes to subalgebras
target: algebraic-envelope-principle
requires: []
---

**(AEP1).**  The Fourier transform `L^2(K, Haar) -> l^2(A)` is a
unitary carrying `L^infinity(K)` onto the group von Neumann algebra
`L(A)` (characters to canonical unitaries), and carrying Haar
integration to the canonical trace `delta_e` — this is exactly where
Haar measure is indispensable: for any other invariant measure the
characters fail to be an orthonormal basis.  A continuous automorphism
of `K` preserves Haar automatically and dualizes to an automorphism of
`A`; the two actions are intertwined by the same unitary.  The crossed
product construction is equivariant under this identification:

```text
L^infinity(K) rtimes Lambda ~= L(A) rtimes Lambda = L(A rtimes Lambda),
```

the last identification being the standard one for a group acting on a
group von Neumann algebra by group automorphisms, and all three carry
their canonical traces to one another.

**(2).**  Suppose `N` is a tracial von Neumann algebra that is not
Connes embeddable and `N` embeds trace-preservingly into
`L^infinity(K) rtimes Lambda ~= L(A rtimes Lambda)`.  If
`A rtimes Lambda` were hyperlinear, its group factor with canonical
trace would embed trace-preservingly into a tracial matrix ultraproduct
`R^omega`-style; restricting that embedding to `N` (the restricted
trace is the trace of `N` by assumption) would make `N` Connes
embeddable — contradiction.  Hence `A rtimes Lambda` is not
hyperlinear.

`A` is countable because `K` is second countable; `A rtimes Lambda` is
countable discrete.  If the action and `K` are effectively presented
(for instance a computable inverse limit of finite abelian groups with
computable `Lambda`-action), `A rtimes Lambda` is recursively
presented, and a Higman embedding places it inside a finitely presented
group, which remains non-hyperlinear because hyperlinearity passes to
subgroups.
