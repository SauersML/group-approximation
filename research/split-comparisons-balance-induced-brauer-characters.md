---
rg: 2
id: split-comparisons-balance-induced-brauer-characters
kind: claim
title: A split comparison between equal-rank finite-subgroup projectives identifies their inductions in every chart-injective finite image
distinct_from:
  nested-two-finite-subgroup-idempotents-have-strict-rank: that compares literally nested idempotents in two finite subgroups by rank; this compares two equal-rank projectives of one finite subgroup joined by arbitrary ambient intertwiners and pushes the comparison to finite images of the actor group.
  lifted-trace-detects-finite-subgroup-projectives: that is an additive trace invariant on K_0 of the ambient algebra; this is an isomorphism statement in finite images, sensitive to conjugacy fusion, which additive invariants of the ambient algebra cannot see.
  subgroup-supported-one-sided-inverse-rigidity: that kills a factor whose support generates a directly finite subgroup; this applies to factors whose support subgroup is arbitrary, provided it has one finite image injective on the chart.
artifacts:
  - research/artifacts/kaplansky-torus-fusion-brauer-balance-2026-09-11.md
---

Let `p` be prime, `G` a group, `K <= G` finite, and `e,f in F_p[K]` idempotents.
Suppose `Z in e F_p[G] f` and `L in f F_p[G] e` satisfy `L Z = f`. Let `H <= G`
contain `K` and the support of `Z`, and let `pi : H -> F` be any homomorphism
to a finite group which is injective on `K`. Then:

1. `Ind_{pi K}^F (f F_p[K])` is isomorphic to a direct summand of
   `Ind_{pi K}^F (e F_p[K])`.
2. If `dim e F_p[K] = dim f F_p[K]`, the two induced modules are isomorphic.
   Hence for every `p`-regular `x in F`

   ```text
   sum over K-classes c with pi(c) inside x^F of
       ( beta_e(c) - beta_f(c) ) / |C_K(c)|  =  0,
   ```

   where `beta` denotes Brauer characters of the right projective modules.

Nothing is assumed about the support of `L`, about `H`, or about `F`.

Consequence: a proposed comparison between two non-isomorphic, equal-rank
projectives of a finite chart can only survive through actors all of whose
chart-injective finite images fuse the classes on which their Brauer
characters differ. Additive invariants of `F_p[G]` never supply this
constraint: they only see the fusion that happens in `G` itself.

ESTABLISHED by [[split-comparison-brauer-balance-proof]]; the complete proof is
Section 1 of the attached artifact.
