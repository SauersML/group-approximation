---
rg: 2
id: stw84-common-stabilizer-wreath-proof
kind: route
title: Factor the common stabilizer and retain the corrected residual fiber bound
target: stw84-common-stabilizer-wreath-bound
requires:
  - stw84-almost-free-permutation-wreath-bound
  - stw84-abelianization-rank-lower-bound
  - stw84-locally-finite-direct-factor-invariance
artifacts:
  - research/artifacts/stw84-common-stabilizer-wreath-2026-08-30.md
---

Write

`W=(direct_sum_S L) rtimes Q`.

Since `H` acts trivially on the lamp group and commutes with `Q`, there is a
literal group isomorphism

`G=H times W`.                                          `(CSW3)`

Both factors are amenable, so

`C*(G)=C*(H) tensor_min C*(W)`.                         `(CSW4)`

Fourier transform and Pontryagin dimension give

`dim_nuc(C*(H))=h`.

For `q>=1`, `stw84-almost-free-permutation-wreath-bound` gives

`dim_nuc(C*(W)) <= (q+1)9^q-1`.

The nuclear-dimension tensor-product inequality applied to `(CSW4)` now
gives

`dim_nuc(C*(G))+1
 <= (h+1)(dim_nuc(C*(W))+1)
 <= (h+1)(q+1)9^q`,

which is the upper bound in `(CSW1)`.  The quotient homomorphism `G->A`
killing the lamp kernel induces `C*(G)->C*(A)`.  Since
`dim_nuc(C*(A))=rank_Q(A)=h+q`, quotient monotonicity supplies the lower
bound.

If `q=0`, then `Q` is locally finite.  The lamp group is locally finite, and
so is its extension `W` by `Q`.  Equation `(CSW3)` and
`stw84-locally-finite-direct-factor-invariance` give

`dim_nuc(C*(G))=dim_nuc(C*(H))=h`,

proving `(CSW2)`.

## Fiber accounting

The factorization is also the precise way to handle the nonfree directions
in the Eckhardt--Wu argument.  At a finitely generated residual stage
`V<=Q`, a central-spectrum fiber fixed by `N<=V` regroups, after passing to
a torsion-free finite-index subgroup, as `B^(tensor K_N)`.  If `B=C`, its
crossed product is `C*(N)` and costs `rank(N)<=q`; if `B!=C`, the strongly
outer Bernoulli argument and finite quotient cost at most one.  Thus the
residual stabilizer-fiber parameter is `max{1,q}`, exactly as in
`stw84-almost-free-permutation-wreath-bound`.

The common subgroup `H` acts trivially on every coefficient fiber.  Rather
than incorrectly treating those directions as strongly outer, `(CSW3)`
extracts their algebra as the commutative tensor factor `C*(H)`, whose
nuclear dimension is exactly `h`.  This accounts for the multiplier `h+1`
in `(CSW1)` and explicitly includes scalar fibers.

In the displayed example, each stabilizer is `H direct_sum <e_n>`, hence is
infinite of rational rank one.  Translation by the `Z`-generator in `Q`
moves one chosen lamp through infinitely many sites, proving failure of the
kernel-finite hypothesis exactly as in the finite-stabilizer example.
