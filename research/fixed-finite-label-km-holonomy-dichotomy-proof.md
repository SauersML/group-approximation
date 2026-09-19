---
rg: 2
id: fixed-finite-label-km-holonomy-dichotomy-proof
kind: route
title: Separate nonscalar face spread from projectively flat finite labels
target: fixed-finite-label-km-holonomy-is-scalar-or-gapped
requires:
  - simple-kazhdan-kac-moody-lattices-exist
  - finite-projective-sector-groupoids-have-conjugate-absorbers
---

Word evaluation in `(FLK1)` factorizes exactly:

```text
r(U)=C_r tensor Q_r.
```

For normalized traces, expansion of the squared Hilbert--Schmidt norm gives

```text
||C_r tensor Q_r-I||_2^2
 =2-2 Re(tau_W(C_r)tau_k(Q_r)).                         (FLK3)
```

Since `|tau_k(Q_r)|<=1`, `(FLK3)` implies `(FLK2)`.  A finite-dimensional
unitary has normalized trace of modulus one only when it is scalar, so the
lower bound is strictly positive whenever `C_r` is nonscalar.

Suppose instead that every `C_r` is scalar.  The tuple `[C_s] in PU(W)` then
satisfies every defining relator, hence induces a homomorphism

```text
bar C:Gamma -> PU(W).                                  (FLK4)
```

If `(FLK4)` were nontrivial, simplicity of `Gamma` would make it injective.
Its image is a finitely generated linear group and hence residually finite by
Malcev.  This would make the infinite simple group `Gamma` residually finite,
which is impossible: a nontrivial finite quotient of a simple group is
injective and therefore cannot be finite.  Thus `(FLK4)` is trivial, so each
`C_s` is scalar.

For a projective sector groupoid, the bisection matrices supplied by
`finite-projective-sector-groupoids-have-conjugate-absorbers` are precisely
such fixed `C_s`.  A scalar direct-sum operator fixes every object sector and
has trivial adjoint label action.  This proves both alternatives and the
claimed no-go.
