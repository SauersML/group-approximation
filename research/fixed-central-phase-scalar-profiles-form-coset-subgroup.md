---
rg: 2
id: fixed-central-phase-scalar-profiles-form-coset-subgroup
kind: claim
title: Scalar finite-phase profiles realizable in one fixed central-character sector form a coset subgroup
distinct_from:
  tensor-affine-selector-pattern-barrier: that is the order-two sign specialization and phrases the conclusion as affine ternary closure; this proves the arbitrary finite-exponent statement by `(m+1)`-fold tensor closure.
  qutrit-psync3-tensor-closure-obstruction: that gives one explicit four-fold order-three counterprofile for fixed-space synchronization; this classifies every scalar order-three profile set, and more generally every order-m profile set, realizable in a fixed phase sector.
  commuting-finite-phase-gadgets-have-affine-scalar-shadows: that assumes the gadget auxiliaries commute and eliminates affine equations syntactically; this permits arbitrary noncommuting auxiliaries and uses only tensor closure of exact representations.
---

**ESTABLISHED.**  Fix an integer `m>=2`.  Let `Gamma` be any group with
distinguished elements

```text
J,z_1,...,z_n,             J^m=z_1^m=...=z_n^m=1,
```

and fix a primitive `m`th root `zeta`.  Let `Sigma_m subset mu_m^n` be the
set of scalar interface profiles `xi=(xi_1,...,xi_n)` for which there is a
nonzero finite-dimensional unitary representation `pi` satisfying

```text
pi(J)=zeta I,                  pi(z_i)=xi_i I.           (FCP1)
```

Then `Sigma_m` is either empty or a coset of a subgroup of `mu_m^n`.

The same conclusion holds for any tensor-closed class of representations,
including representations in finite tracial von Neumann algebras.  No
commutativity assumption is made on auxiliary generators or on the image of
the rest of `Gamma`.

Proof: `fixed-phase-tensor-coset-closure-proof`.

Consequently an ordinary-group gadget cannot have a prescribed scalar
perfect-completeness profile in one fixed central phase unless that profile
is a coset subgroup.  When `m=p` is prime, identifying `mu_p^n` with
`F_p^n` says exactly that the profile is affine.  Noncommuting payloads can
evade the conclusion only by avoiding independently realizable scalar
profiles—for example by using one pointed non-scalar trace whose spectral
atoms are not globally reducing for the gadget.

This is an exact categorical obstruction, not a normalized-HS estimate.  It
therefore applies before any proposed robustification: if perfect scalar
completeness and exact soundness specify a non-coset profile, tensor products
already manufacture a zero-defect forbidden profile.

