---
rg: 2
id: metaplectic-half-shift-ucp-retract-proof
kind: route
title: Tensor by an exact half-projective representation and compress its conjugate pair
target: metaplectic-half-shift-preserves-twisted-fibre-llp
requires:
  - metaplectic-half-class-has-an-exact-finite-model
---

Let `beta(g,h)=exp(pi i b(g,h))`.  By
`metaplectic-half-class-has-an-exact-finite-model` there is a nonzero
finite-dimensional exact projective representation `sigma` of `Gamma` with
multiplier `beta`.

Put `alpha_theta=exp(2 pi i theta b)` and let `u_g^theta` denote the canonical
generator of `A_theta`.  Universality of the full twisted algebras gives
star-homomorphisms

```text
i_theta: A_theta -> A_(theta+1/2) tensor M_(dim sigma),
         u_g^theta |-> u_g^(theta+1/2) tensor conjugate(sigma_g),

j_theta: A_(theta+1/2) -> A_theta tensor M_(dim sigma),
         u_g^(theta+1/2) |-> u_g^theta tensor sigma_g.       (MHS2)
```

Indeed `beta` takes values in `{+1,-1}`, so it equals its conjugate, and the
two multipliers in either line multiply to the multiplier on the source.

Apply `j_theta` to the first tensor factor in the range of `i_theta`.  On a
canonical generator the composite is

```text
u_g^theta |-> u_g^theta tensor sigma_g tensor conjugate(sigma_g).
```

The honest representation `sigma tensor conjugate(sigma)` fixes the
normalized identity vector in the Hilbert--Schmidt realization.  Compression
to that invariant vector is ucp and sends this composite back to `u_g^theta`.
Thus `A_theta` is a ucp retract of a matrix amplification of
`A_(theta+1/2)`.  Interchanging the two parameters gives the reverse ucp
retract.

Finally LLP passes to matrix amplifications and to ucp retracts.  For the
latter statement, if `i:A->B` and `r:B->A` are ucp with `r i=id_A`, compose a
ucp map `phi:A->D/J` with `r`, locally lift `phi r` using LLP of `B`, and
restrict the lift along `i`.  This proves `(MHS1)` in both directions.
