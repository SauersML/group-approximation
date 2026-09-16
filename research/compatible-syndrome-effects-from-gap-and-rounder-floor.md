---
rg: 2
id: compatible-syndrome-effects-from-gap-and-rounder-floor
kind: route
title: Derive compatible local syndrome effects from constant combinatorial gap, a bounded rounder and bounded degree
target: amplifier-has-compatible-local-syndrome-effects
requires: [locality-preserving-constant-combinatorial-gap, amplified-hamiltonian-has-a-constant-cost-rounder]
artifacts:
  - research/artifacts/gap-floor-syndrome-separation-2026-09-16.md
---

**Dead.** Invalidated by
`gap-and-floor-do-not-force-compatible-syndrome-effects`.

## The tempting argument

The NO outputs have combinatorial gap `beta`. Suppose they also admit a
constant-cost rounder, so that the NO energy floor is at least `beta/C`.
Their terms are local, the local dimension is constant and the degree is
bounded. A low-energy input should then be detectable locally. Measure each
term's syndrome with a flag charged to the energy of a bounded neighborhood,
and let recovery repair the reported faults. The flags would give
`W^*B_aW<=C_0 sum_(b in N(a)) h'_b` with occurrence `R`, and the joint
syndrome would never report an infeasible fault set. The constants would be
functions of `beta`, `C`, the locality and the degree.

## Why it fails

The claim gives an explicit unshifted family of norm-one qubit projector
instances. The family has:

- locality two and degree at most `512`;
- combinatorial gap at least `11/30`;
- normalized ground energy at least `1/30`;
- least bare rounder constant at most `11`.

For every `C_0,R`, members with girth at least `3R` and `N^2+1>6C_0R` admit no
tuple satisfying clauses 2 and 3, even with an unrestricted isometry, any
neighborhood sizes, and no realization requirement. Every frustrated set must
have neighborhoods that jointly contain a uniformly gapped subsystem. High
girth and the pair vector `(N,-1)` keep every bounded subsystem nearly
frustration-free. So the premises of the inference hold with uniform
constants while its conclusion fails.

## What survives

Only the generic inference is invalidated: it uses no property of the
amplifier beyond those listed above, and those properties do not suffice.
The target itself is not refuted. Positive shift satisfies clauses 1 to 3
trivially, and once the YES margin is included the anchored criterion
containing the target is equivalent to the root claim, by
`research/artifacts/qpcp-positive-shift-audit-2026-09-11.md`. A construction
for an unshifted amplifier must use further structure
of the amplifier's outputs, for example a fixed finite term collection or
spectrally robust frustration at bounded scale. The averaged necessary
condition is Corollary 9 of the artifact. Whether gap, floor and a fixed
finite term collection force compatible effects is open.
