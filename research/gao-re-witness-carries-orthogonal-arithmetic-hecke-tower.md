---
rg: 2
id: gao-re-witness-carries-orthogonal-arithmetic-hecke-tower
kind: claim
title: Every Gao RE witness carries the full orthogonal arithmetic Hecke-bimodule tower
artifacts:
  - research/artifacts/sl3-re-hecke-bimodule-audit-2026-08-21.md
distinct_from:
  sl3-lattice-inclusion-is-quasiregular-not-mixing: that describes the source inclusion; this transports its double-coset correspondences through the commuting square of an arbitrary RE witness.
  no-exact-quasi-regular-leak: that concerns one Lambda-central unitary in a matrix ultraproduct; this concerns the coordinate subalgebra and all double-coset bimodules forced by Gao's RE definition.
---

By `sl3-re-over-lattice-iff-re-over-scalars`, assume the equivalent scalar
RE model and write its target as

```text
calA=prod_omega A_k,
D=prod_omega B_k,
```

with `B_k` hyperfinite, and let `pi:M->calA` be the trace-preserving
embedding whose square with `N subset D` commutes.  Put
`U_a=pi(u_a)`.

For distinct double cosets `CaC != CbC`, the closed `N-N` subspaces

```text
K_a=closure(N U_a N),       K_b=closure(N U_b N)
```

are orthogonal in `L^2(calA)`.  Each `K_a` is the bifinite arithmetic
correspondence induced from `C cap aCa^(-1)`, with the same left and right
Jones dimensions as in `L^2(M)`.  Moreover

```text
E_D(U_a)=0                 (a notin C),
E_D(U_(h^n))=0             (n!=0),
```

so the dyadic diagonal is simultaneously a relative Haar unitary and the
generator of an infinite orthogonal tower of bifinite Hecke sectors.  The
Jones dimensions in this tower are unbounded: for `n>=1`, the stabilizer
`C cap h^(-n) C h^n` has index at least `2^(2n)` in `C`.

This is an exact ultraproduct statement, not an exact coordinatewise
decomposition.  Therefore scalar non-RE is reduced to a lifting/coherence
theorem: prove that no ultraproduct inclusion with hyperfinite `B_k` can
carry this entire arithmetic Hecke tower together with the regular trace.
Property `(T)`, co-density, relative Haar orthogonality, or
quasi-normalization separately do not contradict the tower.
