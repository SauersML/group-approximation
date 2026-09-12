---
rg: 2
id: norm-matrix-corona-has-no-proper-isometries
kind: claim
title: A norm matrix corona has no proper isometries
distinct_from:
  matrix-corona-k1-vanishes: that computes `K_1` of the corona and kills index invariants of a marked unitary; this is the elementary direct-finiteness statement that every isometry of the corona is already unitary.
  corona-projection-collapse: that transports a projection commuting with a compressed Kazhdan image into the full commutant; this makes no group or property-(T) hypothesis and only says the corona carries no proper isometry.
artifacts:
  - research/artifacts/finite-memory-pair-kernel-audit-2026-08-23.md
---

ESTABLISHED (standard; folklore direct finiteness of matrix coronas, recorded
here because the finite-memory lane repeatedly proposes proper-corner
shortcuts).  Let

```text
C = prod_n M_(d_n)(Complex) / direct_sum_n M_(d_n)(Complex).
```

If `v in C` satisfies `v* v = 1`, then `v v* = 1`.

Consequently no nonzero projection of `C` is equivalent to a proper
subprojection of itself, so any exact-corona construction which forced a
nonzero projection to be properly infinite would force that projection to
vanish.

**What this does and does not buy the finite-memory lane.**  It is a genuine
exact-corona invariant, so it bypasses approximate rounding entirely.  But the
projections a group presentation can produce exactly in a corona are the
finite-subgroup character projections — finite sums of group unitaries — and
exploiting those is the existing finite-order packet / projection-rank /
rank-monodromy mechanism, not a new torsion-free finite-memory engine.
Ordinary group-word relations between commuting involutions do not select the
one-sided spectral corner needed for proper infiniteness, because projection
order is an additive relation in the group algebra rather than a multiplicative
group-word relation, and the regular finite-dimensional representation realizes
every character sector.
