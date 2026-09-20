---
rg: 2
id: lcs-weighted-conjugacy-halting-gap-source
kind: claim
title: Efficient bounded-width linear-plus-conjugacy instances have a HALT-positive uniform matrix-energy gap
distinct_from:
  lcs-perfect-quantum-completeness-re-hardness: that requires efficient binary-LCS games; this permits involutory conjugacy requirements and asks for a weighted normalized-HS source-energy dichotomy before the proved lowering
artifacts:
  - research/artifacts/lcs-constructive-compiler-2026-09-20.md
  - research/artifacts/lcs-auth-controlled-form-audit-2026-09-20.md
  - notes/lcs-source-toffoli-word-semantics-audit-2026-09-20.md
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

A second global-source audit rules out literal circuit-word authentication,
even with a complete shared Pauli anchor and every valid global group
relation. The exact triple-tensor Toffoli model retains all these word
relations but has squared normalized-HS defect 3/2 in the intended
nonlinear Boolean identity. Separately, triple tensoring an honest
controlled-X port of control trace t forces squared distance at least
3t(1-t) from every literal controlled-X readout, even allowing an arbitrary
decoded projection. Both proofs are in the linked audits; they apply the
existing tensor principle rather than add duplicate general graph claims.

These exclude specified full-space fixed-port repairs, not this source
claim. A model-dependent proper corner or genuinely different non-word
readout remains possible, but needs a global consistency theorem and a
dimension-independent retained-trace bound. Neither has been supplied.
