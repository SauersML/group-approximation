---
rg: 2
id: finite-isotropy-corner-proof
kind: route
title: Average each finite stabilizer and identify the resulting orbit-arrow representation
target: finite-isotropy-relation-is-central-corner
requires: []
---

At each `x`, exactly `m` terms in `(FIC1)` are nonzero.  The Fourier
coefficients therefore define an `L^2` element with
`||p||_2^2=1/m`.  Fiberwise multiplication is averaging in the finite group
`Gamma_x`, so `p^2=p=p^*`.  More explicitly, the coefficient of `u_k` in
`p^2` at `x` is zero if `k` does not fix `x`; if `k` fixes `x`, its `m`
decompositions inside `Gamma_x` each contribute `m^(-2)`, giving `m^(-1)`.

On the support of `1_Fix(g)`, the unitary `u_g` commutes with every diagonal
function.  Hence `p` commutes with `L^infinity(X)`.  Conjugation by `u_h`
sends the stabilizer of `x` to the stabilizer of `hx`, so it leaves the
field of stabilizer averages invariant.  Thus `p` also commutes with every
`u_h` and is central in `P`.  Its identity Fourier coefficient is `1/m`, so
`tau_P(p)=1/m`.

The assignments `a |-> ap` and `v_g |-> pu_g` obey the orbit-normalizer
relations.  In particular, on a measurable set where two group elements give
the same orbit arrow, their ratio lies in the point stabilizer and the
stabilizer average makes the two compressed unitaries equal.  They therefore
define a normal homomorphism `Phi:L(R)->pPp`.  Its image contains `Ap` and all
`pu_g`, which generate `pPp`.

Finally the identity coefficient calculation gives

```text
m tau_P(pu_g)=mu(Fix(g))=tau_R(v_g),
```

and similarly on the algebraic span with diagonal coefficients.  Thus `Phi`
is trace preserving for the normalized corner trace, hence injective, and it
is already onto.  This proves `(FIC2)`.

