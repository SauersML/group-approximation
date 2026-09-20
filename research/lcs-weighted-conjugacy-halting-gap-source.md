---
rg: 2
id: lcs-weighted-conjugacy-halting-gap-source
kind: claim
title: Efficient bounded-width linear-plus-conjugacy instances have a HALT-positive uniform matrix-energy gap
distinct_from:
  lcs-perfect-quantum-completeness-re-hardness: that requires efficient binary-LCS games; this permits involutory conjugacy requirements and asks for a weighted normalized-HS source-energy dichotomy before the proved lowering
artifacts:
  - research/artifacts/lcs-constructive-compiler-2026-09-20.md
---

OPEN. There exist constants k>=1 and rational Delta>0 and a uniform
polynomial-time procedure which, from a machine code x, samples a
polynomial-length identifier of a linear-plus-conjugacy requirement.
A uniform polynomial-time decoder returns its bounded-length variable
names and either a nonempty linear row of at most k distinct variables or a
conjugacy X_i X_j X_i=X_h. The induced finite distribution has positive
weight on precisely the requirements of the source instance.

For the squared normalized-HS energy E and infimum e_* defined in
`lcs-construct-weighted-conjugacy-to-lcs`, require

    x halts       => e_*(x)=0,
    x never halts => e_*(x)>=Delta.

All source variables are self-adjoint involutions. The infimum ranges
over all finite matrix dimensions; no bound on a witnessing dimension
is assumed. A perfect exact matrix solution on halting inputs is a
sufficient stronger positive clause, not required here.

## Attempts

The 2026-09-20 constructive audit completed the downstream lowering:
22 linear rows replace a conjugacy, with dimension-independent energy
control. Five extra random bits select a bundle row, and constant-size
identity padding gives an exact fair-bit sampler whose variable selection
is uniform within each final row. The source family above remains
unconstructed.

Culf--Mastel's source constraints include forbidden spectral projections,
not just these ordinary involutory words. Slofstra's word-triviality tag
has the opposite halting orientation. The fixed killed-mark seed route
is also excluded by `lcs-switch-marked-seed-transport-is-re` when its
negative branch admits those finite transport certificates. None of
these supplies the present source family.
