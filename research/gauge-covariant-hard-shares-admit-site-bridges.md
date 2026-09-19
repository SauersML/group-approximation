---
rg: 2
id: gauge-covariant-hard-shares-admit-site-bridges
kind: claim
title: Gauge covariance supplies exact prefix-preserving bridges to independent pulse sites
distinct_from:
  gauge-doubling-gives-selector-flip-symmetries: that constructs the constraint-preserving flip action and a covariant marked representation; this uses its spectral balance to build the site bridge unitaries required by the first-hit reservoir.
  prefix-preserving-two-step-hard-bridge-localizes-exit: that proves the finite-dimensional HS localization estimate from supplied bridge relations; this proves exact marked completeness of those relations after amplification.
  fanizza-hard-exits-attach-to-thompson-site-pulses: that must finitely present the whole bridge orbit and prove polynomial approximate control; this closes only its exact-representation clause.
---

Let `pi` be an exact marked representation of a gauge-doubled BCS, made
covariant as in `gauge-doubling-gives-selector-flip-symmetries`, and assume
`pi(J)=-I`.  For every private share involution `A_n`, its gauge flip is

```text
A_n -> J A_n=-A_n.                                    (GCS1)
```

The implementing gauge unitary conjugates `pi(A_n)` to `-pi(A_n)`.  Hence its
`+1` and `-1` spectral multiplicities are equal.

Adjoin at every independent pulse site two fresh qubits with

```text
a_n=Z tensor I,       B_n=I tensor Z,
s_n=the tensor swap.                                  (GCS2)
```

After a common finite or countably infinite amplification, there is a unitary
`u_n`, acting only on the original representation space and the `n`th fresh
site, such that

```text
a_nu_n=u_nA_n.                                        (GCS3)
```

Because every earlier pulse `B_k` acts on a different fresh site,

```text
[u_n,B_k]=1                         (k!=n).             (GCS4)
```

Thus all exact bridge and prefix relations required by
`prefix-preserving-two-step-hard-bridge-localizes-exit` admit a simultaneous
marked representation.  The construction does not identify any shared
logical BCS variable with a site-local central selector and therefore adds no
cross-context logical commutation.
