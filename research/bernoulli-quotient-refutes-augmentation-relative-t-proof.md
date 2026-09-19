---
rg: 2
id: bernoulli-quotient-refutes-augmentation-relative-t-proof
kind: route
title: Push Bernoulli dual measures through the global-sign quotient
target: infinite-permutation-augmentation-pair-fails-relative-t
requires: []
---

Identify

```text
widehat(L)={+1,-1}^X.
```

For `0<q<1/2`, let `nu_q` be the product probability measure whose
coordinates are independent and take the value `-1` with probability `q`.
It is invariant under every permutation of `X`.  Restriction of characters
gives an `A`-equivariant quotient map

```text
r:widehat(L)->widehat(M).                                (1)
```

Its kernel consists of the two constant characters: equivalently, `(1)`
identifies a configuration with its global sign flip.  Hence every fiber has
two points.  The product measure `nu_q` is atomless because `X` is infinite,
so its pushforward

```text
mu_q=r_*nu_q                                             (2)
```

is also atomless and is `A`-invariant.

On `H_q=L^2(widehat(M),mu_q)`, let `M` act by character multiplication and
let `A` act by its measure-preserving Koopman representation:

```text
(pi_q(m)f)(chi)=chi(m)f(chi),
(pi_q(a)f)(chi)=f(a^(-1)chi).                           (3)
```

The covariance identity in `(3)` makes `pi_q` a unitary representation of
`M rtimes A`.  Its constant unit vector `xi_q=1` is fixed by all of `A`.
If `m in M` has finite support of size `k` (necessarily even), then the
Fourier transform of `(2)` gives

```text
<pi_q(m)xi_q,xi_q>=(1-2q)^k,
||pi_q(m)xi_q-xi_q||_2^2=2-2(1-2q)^k -> 0.             (4)
```

Thus `xi_q` is asymptotically invariant under every fixed finite subset of
`Gamma`: actor elements fix it exactly, and `(4)` handles the finitely many
module components.

It remains to show that no representation in this family has an
`M`-invariant vector.  If `f in H_q` is fixed by every `m in M`, then

```text
(chi(m)-1)f(chi)=0                                      (5)
```

for every `m`.  Since `M` is countable, `(5)` says that `f` is supported,
up to one common null set, on the trivial character of `M`.  The preimage of
that character under `r` is the two constant configurations, which have
`nu_q`-measure zero.  Therefore it has `mu_q`-measure zero and `f=0`.

The representations `(3)` and vectors `(4)` violate the defining criterion
for relative property `(T)` of `(Gamma,M)`, proving the claim.
