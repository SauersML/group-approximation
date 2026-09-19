---
rg: 2
id: ideal-block-choi-feasibility-proof
kind: route
title: Split off the forced scalar quotient block and retain the ideal Choi cone
target: finite-packet-triangle-repair-is-ideal-block-choi-feasibility
requires:
  - simple-kazhdan-kac-moody-lattices-exist
---

Because `B` is finite-dimensional, its ideal `J` is a central summand with
unit `z`, and

```text
B=J (+) (1-z)B.
```

The representation `rho` descends to a surjective finite-dimensional
representation

```text
rho_bar:Q->B/J=(1-z)B.                                    (1)
```

Every finite-dimensional unitary representation of `Lambda` is trivial.
Indeed a nontrivial representation of the infinite simple group would be
faithful; its finitely generated linear image would be residually finite by
Malcev, forcing `Lambda` to be residually finite, which an infinite finitely
generated simple group cannot be.  Therefore `(1)` is the augmentation
character, proving `(IBC3)`.

Suppose `(a)` holds and set `psi=rho o(t+d)`.  Replacing `d` by its
self-adjoint symmetrization does not change `rho o d`, because `psi-rho o t`
is already self-adjoint; the self-adjointness of `L` keeps the symmetrized map
in `L_sa(E,L)`.  Central compression by `z` is
a star homomorphism `B->J`, so

```text
theta(x):=z psi(x)
```

is completely positive and `theta(1)=z`.  Since `rho(d(x)) in J`,

```text
theta=z rho o t + rho o d,
```

and `(b)` follows.

Conversely suppose `(b)` holds, so for some `d:E->L`,

```text
theta=z rho o t+rho o d in UCP_z(E,J).                    (2)
```

Since `d(E) subset I`, its image is killed by `1-z`.  Equations `(IBC3)` and
`(2)` give

```text
rho o(t+d)(x)=theta(x)+epsilon(x)(1-z).                    (3)
```

The two terms in `(3)` lie in orthogonal central summands.  The first is ucp
relative to the unit `z`, while the second is the scalar ucp map relative to
the unit `1-z`.  Their direct sum is therefore ucp into `B`, proving `(a)`.

Finally, `E`, `J`, and `L` are finite-dimensional.  Thus
`UCP_z(E,J)` is a closed relative-unital slice of a finite-dimensional
matrix-ordered Choi cone, and the other set in `(IBC4)` is a
finite-dimensional affine space.  Taking `rho` to be the direct sum of a
packet incorporates all its coordinate conditions at once.

For the dual formulation, work in the real vector space of self-adjoint maps
`E->J`.  The direction space `rho_* L_sa(E,L)` is finite-dimensional and hence
closed, while `UCP_z(E,J)` is compact.  If the affine space in `(IBC4)` is
disjoint from that compact convex set, finite-dimensional strong separation
gives a real functional bounded above on the affine space.  Boundedness on an
affine space forces the functional to annihilate its direction space; after
choosing orientation and translating the strict inequality, this is `(IBC6)`.
Conversely `(IBC6)` plainly excludes an intersection.  No infinite-level
separation theorem is being used.
