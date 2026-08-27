---
rg: 2
id: noncommutative-checksum-misses-bounded-types
kind: claim
title: A summable noncommutative checksum cannot resolve infinitely many bounded-dimensional packet types
distinct_from:
  summable-abelian-checksum-misses-infinite-characters: that uses scalar characters of an abelian group; this permits arbitrary noncommuting matrix-valued packet labels and identifies unbounded representation dimension as the only compactness escape.
  finite-normalizer-star-no-go: that gives an exact Plancherel countermodel for one finite packet and its automorphism normalizers; this treats an infinite library of inequivalent packet types and does not assume a finite normalizer model.
  bounded-hs-loss-kills-static-heavy-tail-library: that dilutes disjoint carrier projections; here both packet types occupy equal macroscopic halves and the checksum fails because their bounded-dimensional labels are precompact.
  multiscale-square-function-checksum-forces-hs-floor: that assumes orthogonal decoded domains and a backward carrier recurrence; this proves that replacing abelian labels by bounded-width noncommutative packets does not construct either ingredient.
---

ESTABLISHED.  Let `M` be a group, let `(m_n)_(n>=0)` be a sequence in
`M`, and let `a_n>=0` with

```text
sum_n a_n < infinity.                                      (SNC1)
```

Fix `k>=1`, and let `Omega` be an infinite set of pairwise inequivalent
irreducible unitary representations `rho:M->U(k)`.  For every `epsilon>0`
there are distinct `rho,sigma in Omega` and a unitary `V in U(k)` such that

```text
sum_n a_n ||rho(m_n)-V sigma(m_n)V^*||_(2,k)^2 < epsilon.  (SNC2)
```

Put `sigma'=Ad(V) o sigma`, let `pi=rho direct_sum sigma'`, and let `C`
swap the two `k`-dimensional summands.  Then the two isotypic projections
`P_rho,P_sigma` satisfy

```text
sum_(theta in {rho,sigma})
  ||C P_theta C^*-P_theta||_(2,2k)^2 = 2,                (SNC3)
```

while the complete weighted noncommutative covariance library satisfies

```text
sum_n a_n ||C pi(m_n) C^*-pi(m_n)||_(2,2k)^2
 = sum_n a_n ||rho(m_n)-sigma'(m_n)||_(2,k)^2
 < epsilon.                                               (SNC4)
```

The same conclusion holds if `Omega` has uniformly bounded, rather than
constant, dimension: pass to an infinite constant-dimension subfamily.

Thus noncommutativity by itself does not evade the heavy-tail compactness
obstruction.  A static summable library of bounded-width matrix packets
cannot control fine type transport, even though every carrier has fixed
macroscopic density and every pair of types is inequivalent.  A viable
noncommutative escape must use at least one of:

1. packet dimensions tending to infinity;
2. a nonsummable orthogonal-domain square function inside one operator; or
3. a backward recurrence that returns every deep mismatch to one fixed
   positive-density carrier.

In particular, translating one fixed finite Toeplitz, Schur, Clifford, or
Heisenberg head packet through infinitely many addresses is still a
bounded-width construction.  Without an additional growing packet or
matrix-only return, changing scalar characters into noncommuting head types
does not establish `self-similar-square-function-checksum-compiler`.
