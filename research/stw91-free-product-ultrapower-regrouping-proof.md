---
rg: 2
id: stw91-free-product-ultrapower-regrouping-proof
kind: route
title: Put the factor splittings in one Fubini ultrapower and regroup four free copies
target: stw91-reduced-free-products-preserve-selflessness
requires: []
---

Selflessness gives nonprincipal ultrafilters `omega_A,omega_B` and
trace-preserving embeddings

```text
alpha:(A,tau)*(A,tau) -> (A^omega_A,tau^omega_A),
beta :(B,sigma)*(B,sigma) -> (B^omega_B,sigma^omega_B),
```

whose restrictions to the first free factors are the diagonal maps.  This is
the free-product-to-ultrapower direction in the definition.

Let `Omega=omega_A tensor omega_B` be the Fubini product ultrafilter on
`N x N`.  Sequences depending only on the first, respectively second,
coordinate give trace-preserving embeddings

```text
A^omega_A -> A^Omega,             B^omega_B -> B^Omega. (1)
```

Use the canonical trace-preserving inclusions `A,B->C=A*B` coordinatewise to
regard the two targets in (1) as subalgebras of `C^Omega`.

The subalgebras `A^Omega` and `B^Omega` are free with respect to `rho^Omega`.
Indeed, take an alternating word of centered ultrapower elements.  For a
representative `(a_s)` from `A`, replace every coordinate by
`a_s-tau(a_s)1`; the removed scalar sequence represents zero because its
`Omega`-limit is zero.  Do the same for the `B` representatives.  The trace
of the resulting alternating word is zero in every coordinate by freeness of
`A` and `B` inside `C`, hence is zero in the ultrapower.  This proves the
claim.

Let `A_1,A_2` be the two copies of `A` supplied by `alpha` in `A^Omega`, and
let `B_1,B_2` be the two copies supplied by `beta` in `B^Omega`.  The pairs
`A_1,A_2` and `B_1,B_2` are internally free because `alpha` and `beta` are
trace-preserving maps from reduced free products.  The preceding paragraph
makes their generated algebras free from one another.  Thus the four copies
are jointly free in `C^Omega`.

Associativity and permutation invariance of the reduced free product now
regroup these four copies as

```text
(A_1*B_1) * (A_2*B_2) ~= C*C.                         (2)
```

The universal reduced-free-product map from (2) into `C^Omega` is
trace-preserving.  Its source trace is faithful because `tau` and `sigma`
have faithful GNS representations; therefore the map is injective.  On the
first copy `A_1*B_1`, both factor maps are diagonal, so its restriction is
exactly the diagonal embedding `C->C^Omega`.  We have constructed

```text
(C,rho)*(C,rho) -> (C^Omega,rho^Omega)
```

in the required direction, fixing the first factor.  Also `C!=C_scalar`
because it contains the non-scalar algebra `A`.  Hence `(C,rho)` is selfless.

For groups, the canonical trace-preserving identification

```text
(C*_r(G),tau_G)*(C*_r(H),tau_H) ~= (C*_r(G*H),tau_(G*H))
```

gives the corollary.

**Trust boundary.**  Faithfulness is used twice: the input traces give the
faithful reduced-free-product trace, and that faithfulness turns the
trace-preserving universal map into an embedding.  No arrow from an
ultrapower to a free product is asserted.
