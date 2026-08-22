---
rg: 2
id: manzoor-isotropy-has-no-positive-finite-type-corner
kind: claim
title: The Manzoor IRS has no positive finite-isotropy corner
distinct_from:
  finite-isotropy-relation-is-central-corner: that gives the positive central-corner construction for finite stabilizers; this proves its hypothesis fails maximally for the non-cohyperlinear IRS on a torsion-free free group.
  cdi-torsionization-needs-schur-multiplier-separation: that asks whether a projective multiplier can be replaced by a finite scalar extension; this concerns the ordinary trivial-isotropy sector of the relation realization, not scalar projective phases.
---

The ergodic non-cohyperlinear IRS used in the Manzoor relation construction is
an IRS of a torsion-free free group `F`.  Its stabilizer is infinite almost
surely.  Consequently the finite-isotropy projection `(FIC1)` has no
positive-trace analogue for this source, and cutting by any fixed finite
subgroup type cannot turn the full-group fixed-point character into the
non-CE relation trace.

More generally, the trivial representation of an infinite stabilizer `H`
does not occur as a normal positive-trace sector of `L(H)`: the left regular
representation on `l^2(H)` has no nonzero `H`-invariant vector.  Averaging a
finite subgroup of `H` only removes that finite subgroup; the remaining
infinite isotropy still has no trivial regular sector.  Hence a finite-type
central corner cannot repair the singular quotient in
`free-actor-extensions-cannot-host-nonce-relation`.

