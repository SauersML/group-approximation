---
rg: 2
id: mihailova-actor-liftable-ce-proof
kind: route
title: Read the quasi-regular coefficient from the centered lamp in exact actor lifts
target: mihailova-actor-liftable-ce-forces-q-hyperlinear
requires: []
---

Let `e` denote the identity of `Q` and abbreviate `a=a_e`.  The Bernoulli
lamps satisfy

```text
w_g a_q w_g^* = a_(g.q),
tau(a_q a_r) = 1_(q=r).                              (AL2)
```

Choose uniformly bounded representatives `A_n in M_(d_n)` of `Theta(a)`.
Because `Theta` is trace preserving and `(AL1)` represents the actor by exact
projective homomorphisms,

```text
lim_(n->omega) tr_(d_n)(
  A_n^* V_n(g) A_n V_n(g)^*)
 = tau(a w_g a w_g^*)
 = 1_(g.e=e).                                        (AL3)
```

Also `||A_n||_2 -> 1`.  On the finite-dimensional Hilbert space
`L^2(M_(d_n),tr_(d_n))`, define the **exact** unitary representation

```text
sigma_n(g)(T) = V_n(g) T V_n(g)^*.
```

After normalizing `xi_n=A_n/||A_n||_2`, equation `(AL3)` says

```text
<sigma_n(g) xi_n,xi_n> -> 1_(g.e=e).                 (AL4)
```

The right side is the cyclic positive-definite coefficient of the
quasi-regular representation `lambda_(G/Stab(e))`, identified with the
given action on `ell^2(Q)`.  Applying `(AL4)` to `g^(-1)h` gives convergence
of every matrix coefficient on the orbit of the cyclic vector.  Thus this
quasi-regular representation is weakly contained in a direct sum (or an
ultraproduct) of the finite-dimensional representations `sigma_n`.

For the canonical left-right action associated to `pi:F_m->Q`, the classical
criterion recorded by Alekseev--Thom,
[*On finite local approximations of isometric actions of residually finite
groups*](https://arxiv.org/abs/2512.14147), Introduction (citing
Brown--Ozawa, Theorem 6.2.7 and Exercise 6.2.4), says that this
finite-dimensional weak containment holds if and only if `Q` is hyperlinear.
This proves the claim.

The proof also locates exactly where bare Connes embeddability stops.  If
`U_(g,n)` are arbitrary representatives of `Theta(w_g)`, then
`T |-> U_(g,n) T U_(g,n)^*` has the coefficient limit `(AL3)`, but it is only
an approximate representation of `G`.  Neither a diagonal representative
for `Theta(B)` nor coordinatewise normalizer membership changes that fact.
The levelwise projective-homomorphism condition `(AL1)` is the entire
promotion gate; scalar defects do not matter because `Ad` kills them.
