---
rg: 2
id: finite-kernel-nonrf-has-central-prime-reduction-proof
kind: route
title: Isolate the invisible kernel, centralize it, and retain a prime quotient
target: finite-kernel-nonrf-has-central-prime-reduction
requires:
  - finite-normal-quotient-residual-formula
  - finite-residual-transports-across-commensurability
artifacts:
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

Residual finiteness of `H` gives `R=R(E)<=K`. The conjugation map
`c:E->Aut(K)` has finite target, so it kills `R` and gives `R<=Z(K)`.
Choose a product `f` of finite homomorphisms detecting each element of
the finite set `K minus R`. Then `L=ker(f) intersect ker(c)` is normal
of finite index in `E`, contains `R`, and satisfies `L intersect K=R`.
Since `L` centralizes `K`, it centralizes `R`.

The image `H_0` is normal of finite index in `H`, with `L/R~=H_0`.
Finite-index heredity gives `R(L)=R`. Choose a maximal proper subgroup
`B<R`: since `R` is nontrivial finite abelian, `R/B~=C_p` for a prime `p`.
Centrality makes `B` normal in `L`, and the finite-normal-quotient formula
gives `R(L/B)=R/B`.

Finally `pi^(-1)(H_0)=KL`, and the index identity follows from
`[KL:L]=[K:K intersect L]=[K:R]`. Finite-index passage and quotients or
surjections with finite kernel preserve word-hyperbolicity. Section 3 of
the artifact supplies the full argument, including the metric estimate
for a finite-kernel map and why one must isolate `R` before projecting
the kernel onto a prime cyclic group.
