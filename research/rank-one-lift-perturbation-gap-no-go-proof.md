---
rg: 2
id: rank-one-lift-perturbation-gap-no-go-proof
kind: route
title: Rank-one surgery preserves the tracial ultraproduct class while destroying the lift gap
target: rank-one-lift-perturbation-gap-no-go
requires: []
---

Take `Gamma=SL_3(Z)`.  It has property `(T)`.  For primes `p -> infinity`,
reduce modulo `p` and take the complex augmentation representation of the
2-transitive action of `SL_3(F_p)` on the projective plane.  The augmentation
representation is irreducible and has dimension

```text
d_p = p^2+p -> infinity.
```

Write it as `rho_p : Gamma -> U(d_p)`.  Since every `rho_p` is irreducible,
the fixed vectors of the conjugation representation on `L2(M_(d_p))` are
exactly the scalars.  Property `(T)` therefore gives a dimension-independent
adjoint spectral gap on the trace-zero subspace.  It follows that for
`pi=[rho_p]_omega`,

```text
pi(Gamma)' cap M_omega = C.
```

Fix a rank-one projection `q_p`.  For each generator `s`, alter
`rho_p(s)` by a unitary on the at-most-two-dimensional span of
`q_p C^(d_p)` and `rho_p(s) q_p C^(d_p)` so as to obtain a unitary `v_(s,p)`
that commutes with `q_p`.  Concretely, choose a unitary `R_(s,p)` supported on
that two-dimensional span and sending `rho_p(s)e_p` to `e_p`, and put
`v_(s,p)=R_(s,p)rho_p(s)`.  Then

```text
[v_(s,p),q_p]=0,
||v_(s,p)-rho_p(s)||_2 = O(d_p^(-1/2)).
```

Now perturb the finite tuple `(v_(s,p))_(s in S)` by arbitrarily small,
generator-dependent unitaries to a tuple `(g_(s,p))` whose joint commutant is
exactly `C`.  Irreducible tuples are dense: perturb one generator to simple
spectrum, then perturb a second so that every matrix entry in the first
one's eigenbasis is nonzero; no proper span of eigenvectors is then invariant
under both.  Choose the perturbation so small that

```text
max_s ||g_(s,p)-v_(s,p)||_op <= d_p^(-2).
```

Then `[g_(s,p)]_omega=[rho_p(s)]_omega`, hence these are lifts of the **same**
ultraproduct representation `pi`, while at every finite level

```text
A_p={g_(s,p):s in S}'=C.
```

Thus `prod_omega A_p=C=pi(Gamma)' cap M_omega`: exact algebraic centralizer
capture holds on the nose.

But `q_p` is still almost invariant under conjugation.  Put
`x_p=q_p-d_p^(-1)1`.  Then

```text
||x_p||_2^2 = d_p^(-1)(1-d_p^(-1)),
||[g_(s,p),x_p]||_2 = ||[g_(s,p),q_p]||_2
                     <= 2 d_p^(-2).
```

Therefore

```text
sum_s ||[g_(s,p),x_p]||_2^2 / ||x_p||_2^2
 <= 4 |S| d_p^(-4) / (d_p^(-1)(1-d_p^(-1)))
 -> 0.
```

The only minimal projection of `A_p=C` is `1`, so its compressed adjoint gap
tends to zero and the total trace of bad minimal blocks is identically `1`.
This contradicts the conclusion of
`kazhdan-centralizer-capture-forces-most-block-gaps`.

The flaw in the invalidated proof is exactly visible here.  The normalized
vectors `x_p/||x_p||_2` have operator norm of order `sqrt(d_p)`.  They define a
unit vector in the Hilbert-space ultraproduct but no uniformly bounded element
of the tracial algebra ultraproduct.  Algebraic relative-commutant capture
therefore has nothing to say about them.
