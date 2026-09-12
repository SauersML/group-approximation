---
rg: 2
id: universal-finite-packet-library-can-be-amenable
kind: claim
title: A two-generated amenable group contains every finite packet at its exact Plancherel fraction
artifacts:
  - research/artifacts/adversarial-error-delocalization-program-2026-08-21.md
distinct_from:
  infinite-index-does-not-force-supercritical-site-rank: that gives tensor-cancellation windows for one Clifford compressor; this gives a universal finite-group library counterexample directly in the canonical trace.
  supercritical-network-needs-noncanonical-cuts: that rules out canonical supercritical branch networks abstractly; this exhibits one amenable host in which every finite packet is already present with its canonical sector weight.
---

There is a two-generated amenable, hence hyperlinear, group `U` which contains
every finite group. More strongly, for every finite subgroup `F<=U` and every
irreducible representation `rho` of `F`, restriction of the canonical regular
representation of `U` to `F` is an infinite multiple of `lambda_F`, and the
central sector idempotent satisfies

```text
tau_U(z_rho)=(dim rho)^2/|F|.
```

Therefore the mere existence of every finite packet, even at its exact positive
Plancherel fraction in one canonical group trace, does not obstruct
hyperlinearity.

The counterexample also meets a literal uniform-carrier formulation. Since
`U` contains `F times C_2` for every finite `F`, every finite configuration can
be placed beneath a commuting sign projection of trace exactly `1/2`. Moreover
`U` is ICC, so its amenable group factor is the hyperfinite `II_1` factor `R`;
inside any prescribed nonzero corner of fixed trace, `R` again contains every
finite-dimensional matrix configuration.

Infinitely many fixed-density packet occurrences are harmless when they
overlap. In an amenable wreath product, conjugate coordinate projections can
all have the same trace `alpha` while finite intersections have trace
`alpha^|S|`. If cross-relations instead force `N` occurrences to be pairwise
orthogonal, then `N alpha<=1` already in the exact regular representation; an
infinite positive-density family would make the intended exact carrier zero.

Thus a successful “universal library” detector cannot use library cardinality
or sector density alone. It needs a finite-dimensional-only multiplicity or
holonomy inconsistency on a reused carrier.
