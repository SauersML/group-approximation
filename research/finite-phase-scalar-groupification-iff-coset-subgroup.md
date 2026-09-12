---
rg: 2
id: finite-phase-scalar-groupification-iff-coset-subgroup
kind: claim
title: Fixed-phase scalar profiles are groupifiable exactly when they form a coset subgroup
distinct_from:
  fixed-central-phase-scalar-profiles-form-coset-subgroup: that proves only necessity for an arbitrary group gadget; this adds the converse by an explicit finite abelian presentation.
  commuting-finite-phase-gadgets-have-affine-scalar-shadows: that eliminates commuting auxiliary variables syntactically; this classifies the scalar interface of every ordinary-group gadget, including gadgets with noncommuting auxiliaries.
  controlled-central-phase-finite-group-barrier: that gives an affine obstruction for a controlled phase; this identifies the complete exact scalar expressive power for every finite exponent.
---

**ESTABLISHED.**  Fix `m>=2`, a primitive `m`th root `zeta`, and a set
`Sigma subset mu_m^n`.  The following are equivalent.

1. There is an ordinary group `Gamma` with distinguished elements
   `J,z_1,...,z_n` of exponent dividing `m` such that `Sigma` is exactly the
   set of scalar profiles `xi` occurring in nonzero finite-dimensional
   representations with

   ```text
   pi(J)=zeta I,                 pi(z_i)=xi_i I.
   ```

2. `Sigma` is empty or a coset of a subgroup of `mu_m^n`.

If `Sigma` is nonempty, `Gamma` in (1) may be chosen finite abelian, with no
auxiliary generators, and every allowed profile is already realized by a
one-dimensional representation.  An empty profile is realized, for example,
by adding the relation `J=1`.

Proof: necessity is
`fixed-central-phase-scalar-profiles-form-coset-subgroup`; sufficiency is
`coset-profile-finite-abelian-presentation-proof`.

Consequently arbitrary noncommuting auxiliaries add no expressive power at
the level of independently realizable scalar interface profiles.  For prime
`m=p`, the exactly groupifiable profiles are precisely affine subspaces of
`F_p^n`.  Any group compiler for a non-affine contextual predicate must
therefore retain non-scalar pointed data; it cannot be repaired by a more
elaborate scalar phase gadget.

