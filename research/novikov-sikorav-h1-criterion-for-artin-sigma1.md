---
rg: 2
id: novikov-sikorav-h1-criterion-for-artin-sigma1
kind: claim
title: "For a finitely presented group, vanishing Novikov-Sikorav homology in degrees 0 and 1 for chi and -chi makes the kernel of a discrete chi finitely generated"
distinct_from:
  bnsr-invariants-stabilize-at-cohomological-dimension: that is stabilization of all Sigma^q at q = cd G; this is only the degree-one criterion, used as an input for explicit Artin groups
---

Let `G` be finitely presented, `X` the presentation 2-complex of a finite
presentation, and `χ : G -> Z` nonzero. Write `\widehat{ZG}_χ` for the Novikov
ring: formal sums `Σ n_g g` with, for every `c`, only finitely many `g` of
`χ(g) < c` and `n_g != 0`.

**Claim.**

1. `[χ] ∈ Σ^1(G) = Σ^1(G; Z)` iff `H_i(X̃ ⊗_{ZG} \widehat{ZG}_{-χ}) = 0` for
   `i = 0, 1`. The convention and the side of the module are fixed by the source.
   The two sign choices differ by `χ -> -χ`.
2. `ker χ` is finitely generated iff `[χ]` and `[-χ]` both lie in `Σ^1(G)`.
   For an Artin group and a discrete `χ`, `[χ] ∈ Σ^1` alone already iff
   `ker χ` is finitely generated.

`X` can stand in for a finite-type `K(G,1)` in degree 1. A `K(G,1)` is obtained from
`X` by attaching cells of dimension `>= 3`, and those cells do not change `H_0` or
`H_1` with any coefficients.
