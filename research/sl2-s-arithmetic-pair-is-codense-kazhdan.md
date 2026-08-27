---
rg: 2
id: sl2-s-arithmetic-pair-is-codense-kazhdan
kind: claim
title: SL2(Z[1/p]) inside SL2(Z[1/pq]) is a finitely generated co-dense (T;FD) subgroup of infinite index
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  dv-s-arithmetic-hs-stable-nonhyperlinear-extension: that is about one lattice and its central extension; this is about a pair of S-arithmetic lattices and the representation-theoretic relation between them.
---

Let `p != q` be primes, `G = SL_2(Z[1/pq])`, `G_0 = SL_2(Z[1/p])`.  Then:

1. `G_0` is finitely generated (finitely presented) and has Lubotzky--Zimmer
   property (T;FD), being an irreducible lattice of S-rank two in
   `SL_2(R) x SL_2(Q_p)` (`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`
   records the same fact for the same group).
2. `[G : G_0] = infinity`.
3. Every finite-dimensional unitary representation `rho` of `G` factors
   through a finite quotient.  Indeed `u = [[1,1],[0,1]]` and
   `d = diag(p, p^(-1)) in G` satisfy `d u d^(-1) = u^(p^2)`, so the
   spectrum of the unitary `rho(u)` is stable under `z -> z^(p^2)`, hence
   consists of roots of unity and `rho(u)` has finite order `N`; the normal
   closure of `u^N` in `G` has finite index (Serre's congruence subgroup
   property for `SL_2` of S-integers with `|S| >= 2`), and `rho` kills it.
4. `G_0` maps onto every finite quotient of `G`: by the congruence subgroup
   property the finite quotients of `G` are quotients of
   `prod_(l != p,q) SL_2(Z_l)`, in which `G_0` is dense by strong
   approximation.

Consequently the pair is **finite-dimensionally co-dense**: for every
finite-dimensional unitary `pi` of `G`, `pi` factors through a finite
quotient `Q` on which `G_0` surjects, so `pi^(G_0) = pi^G`.

Therefore `(G, G_0)` satisfies every hypothesis of
`pauli-lamplighter-over-stable-codense-kazhdan-pair` except the
HS-stability of `G`.  The Pauli lamplighter

```text
Gamma_(p,q) = < SL_2(Z[1/pq]), X, Z, J |
               [X,Z] = J,  [s,X] = [s,Z] = 1 (s in S_0),
               [X, g_1 Z g_1^(-1)] = 1 >,                         (SA1)
```

with `S_0` a finite generating set of `SL_2(Z[1/p])` and `g_1 = diag(q,
q^(-1))`, is a finitely presented group with `J != 1`, and it is
nonhyperlinear if `SL_2(Z[1/pq])` is HS-stable (`sl2-z-inverse-pq-is-hs-stable`).

The same argument works for any pair `SL_2(O_S) <= SL_2(O_(S'))` with
`S subset S'`, `|S| >= 2` including the archimedean places, and for
higher-rank pairs such as `SL_3(Z) <= SL_3(Z[1/p])` where, however, the
big group has property (T) and is therefore not HS-stable.
