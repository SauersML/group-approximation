---
rg: 2
id: constant-outer-weyl-sl3-spectator-proof
kind: route
title: Kill the nonconstant root packet and tensor the outer action by the regular SL3 module
target: constant-outer-weyls-retain-an-sl3-spectator-on-the-deep-star
requires:
  - head-square-whitehead-loop-preserves-deep-star-flag
  - marked-star-outer-corrected-whiteheads-are-quarter-swaps
  - finite-prefix-labelled-windows-remain-projective
---

The coefficient audit in the three prerequisites separates the two kinds of
occurrences.  The `L_i` are words solely in constant roots on the outer
coordinates.  Every other marked-star, prefix, and head root has coefficient
among

```text
q, a_m, b_m, c_m, d_m,
```

or a product which is again a prefix arm or prefix idempotent.  The ordinary
Steinberg rows used in the packet never identify one of these roots with a
nontrivial constant outer root.  Sending all of them to one and retaining
the constant outer roots therefore defines `(OWS4)`.  Formula `(OWS5)` for
`U_i` follows from `U_i=L_iJ_i`; `(OWS6)` verifies the only mixed odd loop.

Now let `rho_0` be the standard finite moving-chart model of the literal
marked/star relation table.  The tensor product

```text
rho(g)=rho_0(g) tensor lambda_K(q(g))                  (1)
```

is again an exact finite-dimensional representation of every relation in
the packet.  All operators used to define the deep star spectral projection
have trivial second factor, proving `(OWS7)`.  The first factor of `L_i` is
the adjacent outer-coordinate label swap, while `(1)` supplies the second
factor in `(OWS8)`.

For a nonidentity element `g` of a finite group, left multiplication on the
group has no fixed point.  Since `ell_i` has order two, its permutation of
`K` is a disjoint union of `|K|/2=84` transpositions.  It has equally many
positive and negative eigenvalues, which proves `(OWS9)`.  The restriction
identity

```text
Res_S^K(lambda_K)=lambda_S^(direct sum [K:S])
```

gives the stated exact `S_3` spectator and its braid.  Finally `(OWS6)` in
the regular representation is exactly `(OWS10)`, completing the fence.
