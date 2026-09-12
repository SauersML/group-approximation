---
rg: 2
id: state-support-corner-exactification-proof
kind: route
title: Compress the bidual by the support of the invariant state
target: state-support-corner-exactifies-near-representation
requires: []
---

Write `u_g=pi(g)`.  Invariance extends normally from `B(H)` to
`M=B(H)**`.  The support projection is characterized as the least projection
`s` with `phi_bar(s)=1`, so uniqueness of support gives

```text
u_g s u_g^*=s.                                           (1)
```

Hence every `u_g` commutes with `s`.

For `d_(g,h)=u_(gh)-u_g u_h`, `(BSC1)` gives
`phi_bar(d_(g,h)^*d_(g,h))=0`.  A normal positive functional is faithful on
its support corner and satisfies `phi_bar(x)=phi_bar(sxs)`.  Therefore

```text
0=phi_bar(s d_(g,h)^*d_(g,h) s)
```

forces `(d_(g,h)s)^*(d_(g,h)s)=0`, hence

```text
d_(g,h)s=0.                                               (2)
```

Using commutation with `s`, equation `(2)` becomes

```text
u_(gh)s=(u_gs)(u_hs).
```

Normalization at the identity and the same equation with `h=g^(-1)` show
that `rho(g)=u_gs` is a unitary representation in the unital corner `sMs`.
The restriction `phi_s` is faithful and normal there.  Invariance implies
that the generators lie in its centralizer (apply invariance to `x u_g`), so
`phi_s` is tracial on `W^*(rho(G))`.

Under `(BSC3)` this trace is the regular group character.  Its GNS vectors
`rho(g)Omega` are an orthonormal basis of the cyclic subspace, and faithfulness
of `phi_s` on the generated von Neumann algebra identifies that algebra
trace preservingly with `L(G)`.  This proves `(BSC4)`.

Every `rho(g)` belongs to the centralizer of `phi_s`, so the modular
automorphism group of `phi_s` fixes `W^*(rho(G))` pointwise.  The restriction
of `phi_s` to that algebra is the finite faithful regular trace.  Takesaki's
conditional-expectation theorem therefore gives a unique `phi_s`-preserving
normal conditional expectation

```text
sMs -> W^*(rho(G)),
```

which is `(BSC5)`.

If `phi` is purely singular, it vanishes on `K(H)`.  Equivalently its normal
extension is supported on the singular central summand of `B(H)**`, so the
support projection need not be represented by a projection in the original
`B(H)`.  The construction supplies only a central state on the corner
`sMs`; extending it invariantly to all operators in a concrete Hilbert-space
representation is an additional amenability assertion.  This is exactly why
the normal-state factorization argument does not extend to the singular
case.
