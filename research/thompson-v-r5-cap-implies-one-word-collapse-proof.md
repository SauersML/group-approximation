---
rg: 2
id: thompson-v-r5-cap-implies-one-word-collapse-proof
kind: route
title: Exactify an arbitrarily large leaf packet and use the minimal degree of the alternating group
target: thompson-v-r5-cap-implies-one-word-collapse
requires:
  - gowers-hatami-finite-group-hs-stability
---

Assume the CAP hypothesis stated in the target.  Let `U` have presentation
defect `delta` in dimension `d`, set `eta=C delta`, and choose a power of two
`N=2^n` so large that

```text
N-1 > d/(1-4 eta^2).
```

For `eta<1/16`, apply Gowers--Hatami to the CAP map `Phi:S_N->U(d)`.  It gives
an exact representation `rho:S_N->U(m)` on a flexible enlargement, with

```text
d <= m <= d/(1-4 eta^2),
||Phi(g)-V^*rho(g)V||_2 <= 42 eta
```

for an isometry `V:C^d->C^m` and every `g in S_N`.

For `N>=7`, the least dimension of a nontrivial complex representation of
`A_N` is `N-1`.  Since `m<N-1`, `rho|_(A_N)` is trivial.  The permutation
`a_N` induced by `(00 01)` on level `n` is a product of `N/4` transpositions;
for `n>=3` this number is even, so `a_N in A_N` and `rho(a_N)=I`.

The Gowers--Hatami estimate and CAP's marked comparison now give

```text
||U(a)-I||_2
 <= ||U(a)-Phi(a_N)||_2+||Phi(a_N)-I||_2
 <= C delta+42 C delta
 =43 C delta.
```

This tends to zero with the presentation defect and proves `(TCAP)`.  The
representation-degree input is the standard minimal-degree theorem for
alternating groups (for example the `A_N` consequence of Rasala's minimal
character-degree theorem); the restriction `N>=7` avoids the small-degree
exceptions.
