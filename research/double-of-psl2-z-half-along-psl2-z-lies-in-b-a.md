---
rg: 2
id: double-of-psl2-z-half-along-psl2-z-lies-in-b-a
kind: claim
title: The double of PSL_2(Z[1/2]) along PSL_2(Z), a finitely presented group that is not residually finite, and its centralizing HNN extensions lie in B_A
distinct_from:
  free-permutational-products-preserve-pbh: that proves centralizing amalgams and doubles over FINITE subgroups; this uses its criterion (part 1) over the infinite vertex stabilizer PSL_2(Z[1/m]), made available by lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a.
  pbh-class-closed-under-common-retract-amalgams: that needs a common retract; PSL_2(Z) is not a retract of PSL_2(Z[1/2]), by the normal subgroup theorem.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `double-of-psl2-z-half-along-psl2-z-proof` (lane proof; not
independently reviewed; no priority claimed).

## Statement

Let `m ≥ 1` be odd, `W = PSL_2(Z[1/(2m)])` and `C = PSL_2(Z[1/m])`.

1. For every `K ∈ B_A`, the centralizing amalgam `W *_C (C × K)` lies in `B_A`. With
   `K = Z` this is the centralizing HNN extension `⟨W, t | t c t^(-1) = c (c ∈ C)⟩`.
2. The double `W *_C W` lies in `B_A`.

All of these are finitely presented, since `W` is finitely presented and `C` finitely
generated, and they embed in finitely presented simple groups.

## Why it is not covered by known methods

- **Not residually finite.** For `m = 1`, the double `D = PSL_2(Z[1/2]) *_{PSL_2(Z)} PSL_2(Z[1/2])`
  is not residually finite.
  - The swap involution of `D` fixes exactly `C` inside the first factor. So residual
    finiteness of `D` would make `C` closed in the profinite topology of `W`.
  - But `PSL_2(Z)` is dense there. By Serre's congruence subgroup theorem for
    `SL_2(Z[1/2])` (cited, not re-read here), every finite quotient of `W` factors through
    some `PSL_2(Z/N)` with `N` odd, onto which `PSL_2(Z)` surjects.
- **Consequences.** So `D` is not linear, not self-similar, and not a subgroup of any
  residually finite host. Hosts for `D` must be non-residually-finite, as here, where `D`
  sits in the finitely presented simple commutator subgroup of a twisted Brin–Thompson
  group.
- **No retraction.** `C` is not a retract of `W`. By Margulis' normal subgroup theorem for the
  irreducible `S`-arithmetic lattice `W` of `PGL_2(R) × PGL_2(Q_2)` (cited), a
  homomorphism onto the infinite group `C` would have finite kernel or finite image. The
  first would make `W` virtually free, but `W` contains `BS(1,4)`.
