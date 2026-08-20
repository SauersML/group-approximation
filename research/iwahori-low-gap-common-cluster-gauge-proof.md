---
rg: 2
id: iwahori-low-gap-common-cluster-gauge-proof
kind: route
title: Use cluster polar rounding as a near-identity conjugating gauge
target: iwahori-low-gap-common-cluster-gauge
requires:
  - mixed-intertwiner-energy-transport-localization
  - block-transport-cluster-unitarization
---

Take `U=I` in `mixed-intertwiner-energy-transport-localization`.  For the
low-gap graph `G_n={lambda_(n,i,j)<a_n}`, the total forbidden overlap mass is

```text
beta_n <= E_n/a_n -> 0.
```

The mass joining different connected components of `G_n` is no larger, so
`gamma_n<=beta_n->0`.  Apply `block-transport-cluster-unitarization` to the
source and target isotypic projections.  After adding at most
`gamma_n d_n=o(d_n)` trivial dimensions to both sides, it gives a direct sum
of component unitaries

```text
V_n=directSum_C V_(n,C)
```

with each `V_(n,C):Q_(n,C)->P_(n,C)` unitary and

```text
||V_n-I_0||_2 <= (1+sqrt(2))sqrt(gamma_n)->0,          (1)
```

where `I_0` is the original identity extended by zero on the padding.
Identifying the two stabilized copies by the natural identity on the added
trivial coordinates changes `(1)` only by the normalized norm of those
coordinates, which is `O(sqrt(gamma_n))`; hence `||V_n-I||_2->0` in the
flexible metric.

Put

```text
R_(n,C)=P_(n,C),
sigma'_n(s)=V_n sigma_n(s)V_n^*.
```

The source cluster projection `P_(n,C)` reduces `rho_n` by construction.
Since `Q_(n,C)` reduces `sigma_n` and `V_n Q_(n,C)V_n^*=P_(n,C)`, the same
`R_(n,C)` reduces `sigma'_n`.  Exact equality of the stabilized cluster ranks
is built into the cluster-unitarization step.

Finally unitary invariance gives

```text
||rho_n(s)-sigma'_n(s)||_2
 =||rho_n(s)V_n-V_n sigma_n(s)||_2.
```

The energy estimate in `block-transport-cluster-unitarization` therefore
implies

```text
sqrt(sum_s||rho_n(s)-sigma'_n(s)||_2^2)
 <= sqrt(E_n)+2sqrt(2|S_B|gamma_n)->0.                 (2)
```

Equations `(1)--(2)` prove the common-cluster gauge statement.