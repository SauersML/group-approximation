---
rg: 2
id: one-britton-commutator-excludes-exact-arithmetic-actor-sector
kind: claim
title: One mixed Britton commutator excludes every exact arithmetic actor sector
distinct_from:
  sl3-prime-coset-action-exact-atlas-firewall: that gives a Hamming lower bound for one-hot coset labels inside exact finite permutation actions; this gives a normalized-Hilbert--Schmidt trace obstruction for every exact finite-dimensional unitary actor, using only the mixed word [t,h].
  sl3-hnn-finite-window-central-dual-gap: that must charge bounded matrix-range separators for arbitrary approximate actor tuples; this closes only the exact-actor stratum, before a separator is needed.
  exact-projective-codensity-has-a-uniform-trace-square-gap: that controls an arbitrary auxiliary unitary against an exact arithmetic representation; this specializes the estimate to the HNN stable letter and identifies a single finite canonical Britton window that makes the exact actor sector infeasible.
---

Fix a prime `p`, put

```text
Lambda=SL_3(Z), Gamma=SL_3(Z[1/p]), h=diag(p,1,1/p),
G_p=<Gamma,t | [t,Lambda]=1>,
```

and fix a finite symmetric Kazhdan generating set `S` of `Lambda`, with
Kazhdan constant `kappa>0` in the normalized Hilbert--Schmidt convention.
There is an explicit `delta_0>0`, depending only on `(S,kappa)`, such that
the following finite packet has no realization in any dimension:

1. `rho:Gamma->U(d)` is an exact finite-dimensional representation;
2. `T in U(d)` satisfies

   ```text
   max_(s in S)||[T,rho(s)]-I||_2 <= delta_0;                    (OB1)
   ```

3. the single canonical mixed-word test satisfies

   ```text
   |tr_d([T,rho(h)])| <= delta_0.                               (OB2)
   ```

For example one may take

```text
delta_0=min(1/4, kappa/sqrt(8|S|)).                              (OB3)
```

Indeed every finite-dimensional unitary representation of the higher-rank
`S`-arithmetic group `Gamma` has finite congruence image away from `p`, and
the integral lattice surjects onto that image.  Hence

```text
rho(Lambda)'=rho(Gamma)'.                                       (OB4)
```

Let `Q` be the Hilbert--Schmidt orthogonal projection onto
`rho(Lambda)'`.  Property `(T)` and `(OB1)` give

```text
||T-Q(T)||_2^2
 <= kappa^(-2) sum_(s in S)||T rho(s)-rho(s)T||_2^2
 <= |S| delta_0^2/kappa^2.                                     (OB5)
```

By `(OB4)`, `Q(T)` commutes with `rho(h)`.  Therefore

```text
||[T,rho(h)]-I||_2
 =||T rho(h)-rho(h)T||_2
 <=2 sqrt(|S|) delta_0/kappa.                                  (OB6)
```

For a unitary `W`,

```text
Re tr_d(W)=1-(1/2)||W-I||_2^2.
```

Equations `(OB3)--(OB6)` yield

```text
|tr_d([T,rho(h)])| >= Re tr_d([T,rho(h)]) >=3/4,                (OB7)
```

contradicting `(OB2)`.

Thus the finite endpoint `sl3-hnn-finite-window-central-dual-gap` is already
true, vacuously and with the one-word window `W={[t,h]}`, on every exact
finite-dimensional arithmetic actor sector.  The same estimate covers any
sector whose actor tuple is sufficiently close to an exact representation,
after adding the elementary word-evaluation Lipschitz error.  A failed
finite-window inequality must therefore be a uniformly noncorrectable actor
outlier; no bounded congruence-depth exact actor or exact finite action can
carry it.
