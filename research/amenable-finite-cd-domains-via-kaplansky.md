---
rg: 2
id: amenable-finite-cd-domains-via-kaplansky
kind: route
title: Kaplansky's zero-divisor conjecture gives domain integral group rings for groups of finite cohomological dimension
target: amenable-finite-cd-integral-group-rings-are-domains
requires:
  - kaplansky-zero-divisor-conjecture
artifacts:
  - research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md
---

## Why sufficient

Let `G` be amenable with `cd_Z G < ∞`.

1. **`G` is torsion-free.** Suppose `C <= G` is cyclic of order `q > 1`. Since `Z[G]` is free as a
   `Z[C]`-module, a projective resolution of `Z` over `Z[G]` is one over `Z[C]`, so
   `cd C <= cd G < ∞`. But `H^{2k}(C; Z) = Z/q != 0` for every `k >= 1`, so `cd C = ∞`, a
   contradiction.
2. **`Q[G]` is a domain.** `kaplansky-zero-divisor-conjecture` covers the field `Q` and the
   torsion-free group `G`.
3. **`Z[G]` is a domain.** It is a unital subring of `Q[G]`, and it is nonzero.

That is the target. ∎

Amenability is not used, and neither is anything specific to `Q`: the conjecture for any field of
characteristic 0 gives the same conclusion, because `Q[G]` is a subring of `k[G]`. See artifact
Lemma 1.2.
