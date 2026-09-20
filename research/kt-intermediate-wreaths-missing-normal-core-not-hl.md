---
rg: 2
id: kt-intermediate-wreaths-missing-normal-core-not-hl
kind: claim
title: Every intermediate Kun--Thom coset wreath missing the normal closure is nonhyperlinear
distinct_from:
  kt-intermediate-coset-wreaths-are-nonsofic: "That excludes sofic models; this excludes every faithful tracial matrix-ultraproduct model with the stronger Liu--Thom normalization input."
  kun-thom-wreath-family-is-not-hyperlinear: "That fixes the lamp stabilizer to Gamma; this allows every intermediate K missing its normal closure, even without property T or infranormality of K."
  kt-pair-hyperlinear-floor-below-normal-closure: "That asserts existence of a hyperlinear member of this family; this is its universal negation."
artifacts:
  - research/artifacts/liu-surjunctivity-permanence-audit-2026-09-20.md
---

For every Kun--Thom Theorem E pair Gamma<=G, put N=<<Gamma>>_G.
For every Gamma<=K<=G such that N is not contained in K, the group

    W_K=(direct_sum_(G/K) C_2) semidirect G

is not hyperlinear. More strongly, every homomorphism from W_K into
a hyperlinear group kills every lamp pair a_(nx) a_x, for n in N and
x in G/K. At least one such pair is nonidentity.

K need not be Kazhdan, infranormal, finitely generated, or normal.
The analytic input is Jihao Liu's internality theorem via Andreas Thom's
conditional normalization theorem for the original pair Gamma<=G.
This extends the earlier Cairn intermediate-coset *sofic* obstruction.

The threshold is attained: for K=N, the existing fibre-parity theorem
identifies W_N with a residually finite quotient of W_Gamma. This does
not by itself assert that every overgroup K>=N gives a residually finite
or hyperlinear wreath; arbitrary further quotients require separate work.
