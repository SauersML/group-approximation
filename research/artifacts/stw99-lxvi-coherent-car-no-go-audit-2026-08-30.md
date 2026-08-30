# STW LXVI: coherent CAR construction no-go audit (2026-08-30)

## Exact open construction boundary

The existing reductions turn Problem LXVI into constructing a simple unital
finite but non-stably-finite algebra containing CAR unitally.  The first
unstable matrix size is irrelevant.  A unital CAR corner is equivalent to a
coherent halving chain in the projection monoid, but neither divisibility in
`K_0` nor independently available finite matrix stages supplies that chain.

Known no-go results already exclude three natural shortcuts:

- tensoring a non-stably-finite finite seed by CAR;
- assembling independent dyadic stages in a simple norm ultraproduct; and
- making the CAR tail asymptotically central when the ambient double is
  infinite.

The finite-index obstruction below is independent of all three.  It assumes
that the coherent CAR copy is already present and instead controls the size
of its ambient module envelope.

## Finite Watatani-index obstruction

Let `D subset A` be unital, with `D` stably finite, and suppose a conditional
expectation `E:A->D` has a finite Watatani quasi-basis `u_1,...,u_r`.  The
quasi-basis identity makes `A`, with `D`-valued inner product
`<x,y>=E(x^*y)`, a finitely generated projective right Hilbert `D`-module.
The proof node avoids treating this as a black box: it writes the associated
corner representation explicitly as

```text
p_(ij)=E(u_i^*u_j),
rho(a)_(ij)=E(u_i^*a u_j),
rho:A->pM_r(D)p.
```

The quasi-basis equations show directly that `p` is a projection, `rho` is a
unital star homomorphism, and `rho` is faithful.  Stable finiteness of `D`
passes to matrix corners and unital subalgebras, so `A` is stably finite.

Taking `D` to be the embedded CAR algebra proves a new construction no-go:
an LXVI ambient algebra or either equivalent finite seed cannot carry a
finite-index expectation onto that CAR copy.  Its coherent dyadic tower must
have genuinely infinite module index in the ambient algebra.

This excludes finite-group crossed products of CAR, finite towers of
finite-index expected extensions, and injective limits assembled from such
stages.  The obstruction uses no trace extension, quasitrace, `K_0`, central
sequence, or simplicity argument.

## Trust boundary

The theorem requires a finite Watatani quasi-basis, not merely a faithful
conditional expectation or a Pimsner--Popa lower bound.  Without a finite
quasi-basis the Hilbert-module completion need not be a finitely generated
projective module, and there is no fixed matrix corner `pM_r(D)p` into which
the ambient algebra must embed.  No obstruction is claimed for infinite-index
expected CAR inclusions.

The finite-index mechanism also does not obstruct a nonexpected, highly
noncentral CAR inclusion.  Such infinite-index inclusions remain the live
coherence frontier after the existing tensor, reduced-product, ultraproduct,
and central-matrix no-go results.
