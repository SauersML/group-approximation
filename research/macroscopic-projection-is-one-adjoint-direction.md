---
rg: 2
id: macroscopic-projection-is-one-adjoint-direction
kind: claim
title: Macroscopic Hilbert carrier mass can occupy vanishing adjoint dimension
distinct_from:
  commutant-density-trace-blind: that computes normalized commutant density from characters and shows regular-character models make it vanish; this is the elementary finite-coordinate mechanism explaining why even a half-rank witness need not affect that density.
  predicate-rank-jump-forces-adjoint-reynolds-gap: that manufactures a positive adjoint-density gap from multiplicity branching; this shows why boundedly many individual witness operators cannot do so.
---

Give `M_d(C)` its normalized Hilbert--Schmidt inner product and give
`End(M_d(C))` the normalized Hilbert--Schmidt norm obtained by dividing its
ordinary Hilbert--Schmidt norm by `d`.  Then:

1. a projection `e in M_d` may have `tr_d(e)=1/2` and `||e||_2^2=1/2`, while
   its linear span has normalized adjoint dimension only `1/d^2`;
2. more generally, the span of any fixed `R` matrix words has normalized
   adjoint dimension at most `R/d^2`;
3. for unitaries `U,V`,

   ```text
   ||Ad(U)-Ad(V)||_(2,adj)^2
      =2(1-|tr_d(U^*V)|^2)
      <=2||U-V||_2^2.                                      (MAD1)
   ```

Thus normalized-HS multiplicativity controls adjoint operators only in an
average `d^2`-dimensional sense.  It can lose a fixed finite orbit of
macroscopic-rank projections at vanishing cost.  A successful adjoint-density
obstruction must create `Omega(d^2)` witness directions, typically through a
multiplicity algebra, rather than merely create one projection of rank
`Omega(d)`.

This is the precise dilution mechanism left open by
`parity-compressor-hs-return`: its half-trace projection is macroscopic on the
original Hilbert space but is still one adjoint vector.

