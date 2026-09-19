---
rg: 2
id: subhomogeneous-energetic-carrier-no-gap-proof
kind: route
title: Disintegrate the carrier trace into bounded matrix factors and extend each factor across the central summand
target: subhomogeneous-energetic-carrier-no-strict-gap
requires: []
---

First suppose `tau(q)>0`.  The normalized restriction

```text
sigma(x)=tau(x)/tau(q),                 x in qAq,
```

is a tracial state on the unital algebra `qAq`.  A subhomogeneous C-star
algebra is type I, and the central disintegration of any tracial state is a
probability barycenter of normalized traces of its finite-dimensional factor
representations.  Concretely there is a probability measure `mu` on factor
representations `rho` of dimensions at most `D` such that

```text
sigma(x)=integral tr_dim(rho)(rho(x)) dmu(rho).           (1)
```

Because `q` is central, every unital representation `rho:qAq->M_r` extends
to a unital representation of `A` by

```text
rho_tilde(x)=rho(qx).
```

Indeed centrality gives `qxy=(qx)(qy)`, and
`rho_tilde(1_A)=rho(q)=I`.  Hence every integrand in `(1)`, evaluated at
`a`, is at most `beta_fd(A,a)`.  Positivity of `a` gives

```text
tau(a)=tau(q)sigma(a)
      <=tau(q)beta_fd(A,a)
      <=beta_fd(A,a).                                    (2)
```

If `tau(q)=0`, then `0<=a<=||a||q` in the corner unitization, so
`tau(a)=0`, and `(2)` still holds.  Taking `tau` to be the canonical group
trace proves `(SEC2)`.

For the finite-orbit statement, the equivalence bimodule `qAp` has a finite
frame of length at most `m`: the mutually orthogonal conjugates of `p` sum to
`q`.  Inducing an irreducible representation of `qAq` to `pAp`, or
equivalently writing it on the `m` packet translates of the `p`-fiber, shows
that its dimension is at most `m` times the dimension of an irreducible
`pAp` constituent.  Thus `pAp` being `D`-subhomogeneous implies `qAq` is
`mD`-subhomogeneous.  Apply the central case.
