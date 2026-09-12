---
rg: 2
id: ergodic-nonce-irs-fg-support-is-terminal
kind: claim
title: Finite generation on an ergodic non-CE IRS support is already terminal
distinct_from:
  atomic-noncohyperlinear-irs-forces-nonhyperlinear: that starts with an atom of the subgroup law and extracts a finite-index regular quotient; this gives a simple intrinsic hypothesis on the random subgroups which forces such an atom.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that conditions on an atom of a finite readable base partition and retains random fiber isotropy; this concerns finite generation of the stabilizer subgroup itself.
  manzoor-isotropy-has-no-positive-finite-type-corner: that excludes finite isotropy corners in the particular construction; this rules out all finitely generated subgroup support unless the group problem is already solved.
---

Let `mu` be an ergodic invariant random subgroup of a countable group
`Gamma`, and suppose its membership character has non-Connes-embeddable
tracial GNS algebra.  If

```text
mu({H<=Gamma:H is finitely generated})>0,                (EFG1)
```

then a countable non-hyperlinear group exists.

Indeed, finite generation is conjugacy invariant, so ergodicity makes the
probability in `(EFG1)` equal to one.  A countable group has only countably
many finitely generated subgroups.  Every probability measure supported on
a countable set has an atom.  The conclusion now follows from
`atomic-noncohyperlinear-irs-forces-nonhyperlinear`.

Consequently the ergodic perfect ZPC-gap witness has the sharp alternative

```text
some stabilizer is an atomic finite-orbit witness and yields a
non-hyperlinear quotient,

or mu-almost every stabilizer is infinitely generated.                 (EFG2)
```

This also explains why refinement through finite quotient images does not
automatically terminate.  The maps

```text
H |-> H N/N <= Gamma/N
```

for finite-index normal `N` give finite invariant partitions and hence the
fiber reductions of `finite-invariant-partition-only-reduces-irs-to-fiber-irs`.
But infinitely generated subgroups of a residually finite group need not be
closed in the profinite topology; distinct dense subgroups can have the same
image in every finite quotient.  Pinning all finite images therefore need
not produce an IRS atom.  A positive use of this refinement must prove
subgroup separability for the actual stabilizers, or retain the non-CE gap
while resolving data beyond their profinite closures.

DERIVATION
ergodic-nonce-irs-fg-support-proof
