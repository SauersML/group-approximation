---
rg: 2
id: sp21-lattice-has-congruence-subgroup-property
kind: claim
title: Some torsion-free cocompact arithmetic Sp(2,1) lattice has the congruence subgroup property
distinct_from:
  normal-subgroups-of-arithmetic-lattices-are-congruence-open: that is an unconditional fact controlling congruence quotients of quotients; this is the open assertion that there are essentially no other finite quotients
  sp21-lattice-hyperbolic-quotient-without-finite-quotients: that asks for one finite-quotient-free hyperbolic quotient; this is a property of the lattice itself which would make every infinite hyperbolic proper quotient non-residually-finite
---

Let `Γ <= G(O)` be a torsion-free cocompact arithmetic lattice in `Sp(2,1)`,
with `G` as in `normal-subgroups-of-arithmetic-lattices-are-congruence-open`.
Assert that the kernel of the natural map `Γ̂ -> Γ̄`, from the profinite
completion onto the congruence completion, is finite.

By `non-rf-hyperbolic-via-sp21-congruence-property` this assertion gives a
non-residually-finite hyperbolic group.  Contrapositive: if every hyperbolic
group is residually finite, no torsion-free cocompact arithmetic `Sp(2,1)`
lattice has the congruence subgroup property.

## Attempts

- **Settling it either way.**  Not attempted here.  Property (T) passes to
  finite-index subgroups, so every finite-index subgroup of `Γ` has finite
  abelianization.  Failure of the property therefore cannot be shown by a
  finite-index subgroup with infinite abelianization.
- **Status boundary.**  The literature status of this property for `Sp(n,1)`
  lattices was not re-read in this pass; nothing here depends on it.
