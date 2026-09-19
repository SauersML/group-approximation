---
rg: 2
id: kazhdan-rf-block-ultralimit-proof
kind: route
title: Put the finite-quotient regular representations under a block-ultralimit charge
target: kazhdan-rf-amenable-near-model-has-no-positive-finite-sector
requires: []
---

Take any infinite residually finite property-(T) group `Gamma` and a
descending finite-index normal chain `Gamma_n` with trivial intersection.
After passing to a subsequence, assume
`|Gamma/Gamma_n| -> infinity`. Put

```text
F_n=Gamma/Gamma_n,
H=directSum_n ell^2(F_n),
X=disjointUnion_n F_n,
pi=directSum_n lambda_(F_n).
```

For a nonprincipal ultrafilter `omega`, define

```text
mu(A)=lim_(n->omega) |A intersect F_n|/|F_n|.
```

Each left translation preserves uniform measure on every `F_n`, so `mu`
and the induced state `mu_bullet` are `pi(Gamma)`-invariant. Since `pi`
is a homomorphism, its near-representation defect is zero. The residual chain
makes `pi` faithful; for each nonidentity `g`, its action is eventually a
nonidentity left translation and hence has no fixed basis vector. Thus the
model is essentially free in the Kahl--Schneider sense.

Let `P_n` be the projection from `H` onto `ell^2(F_n)`. The induced
state on a finite-rank projection `P` is

```text
mu_bullet(P)
 =lim_(n->omega) Tr(P_n P P_n)/|F_n|.
```

Positivity and trace monotonicity give

```text
0 <= Tr(P_n P P_n) <= Tr(P)=rank(P).
```

The denominator tends to infinity, so the ultralimit is zero. Every
finite-dimensional invariant subspace has a finite-rank orthogonal
projection, proving the claim. QED
