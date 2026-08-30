---
rg: 2
id: property-t-free-spectator-erases-old-commutant-overlap
kind: claim
title: A non-Kazhdan congruence spectator erases old-commutant overlap without erasing local Schur density
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that creates positive local Reynolds density from forbidden packet mass; this shows that density need not have positive overlap with the old-group low spectrum.
  canonical-marked-corner-nonamenable-density-vanishes: that excludes low-energy density in canonical regular trace; this is an arbitrary finite-dimensional spectator model and explains why the canonical terminal cannot authenticate norm-corona traces.
---

**ESTABLISHED PROPERTY-`(T)`-FREE COUNTERMODEL.**  Let
`Lambda=SL_2(Z)`.  For primes `p`, let `sigma_p` be the dimension-`p`
Steinberg irreducible of `SL_2(F_p)`, pulled back along reduction modulo
`p`.  Let a finite packet act on a fixed space `K`, let `R_K` be any
nonzero local Reynolds-difference projection in `End(K)`, and form

```text
H_p=K tensor V_p.
```

The packet acts on `K` and `Lambda` acts through `sigma_p` on `V_p`.  Then:

1. the local Reynolds range `R_K tensor End(V_p)` has the same normalized
   adjoint density `delta=rank(R_K)/dim(K)^2` for every `p`;
2. the `Lambda`-fixed adjoint space is exactly
   `End(K) tensor C I_(V_p)`;
3. the intersection of these two spaces has normalized density

   ```text
   delta/p^2 ->0;                                      (PFS1)
   ```

4. for one fixed generating measure on `SL_2(Z)`, the adjoint action has a
   uniform spectral gap off that fixed space.

The last assertion uses the congruence property `tau` of `SL_2(Z)`, not
property `(T)` (which `SL_2(Z)` does not have).  Hence even a uniform
property-`(T)`-free old-group gap does not couple a positive-density local
Schur carrier to the old commutant.  A coefficient-covariance cell must
exclude this tensor spectator explicitly.

DERIVATION
property-t-free-spectator-overlap-proof

