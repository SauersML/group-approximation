---
rg: 2
id: two-unitary-corner-amitsur-proof
kind: route
title: Halmos-dilate the Fock letters and test the standard polynomial in the fixed corner
target: one-sided-amitsur-oracle-has-two-unitary-corner-model
requires:
  - one-sided-amitsur-oracle-has-bounded-fock-model
  - two-generator-amitsur-levitzki-dimension-oracle
---

For an isometry `V`, its defect `D=I-VV^*` satisfies
`D^2=D`, `DV=0`, and `V^*D=0`.  Direct block multiplication then proves that
`[[V,D],[0,-V^*]]` is unitary and has upper-left compression `V`.  Apply this
simultaneously to the two Fock creation isometries.  Since every multiplication
in `(TUC1)` occurs in the fixed upper-left corner, its value is exactly the
old Fock value, proving `(TUC5)`.

In a `2d`-dimensional evaluation, the same fixed corner has dimension `d`.
The standard polynomial `s_(2d)` vanishes on all endomorphisms of that corner,
whether or not the compressed unitary letters remain isometries.  Hence the
`d`th residual is `-P`, and normalization in the whole `2d`-dimensional space
gives `1/sqrt(2)`.

Finally, the canonical trace calculation `(TUC7)` audits the scope of the
construction: a fixed group-algebra decoder cannot promote the two proper
Fock isometries themselves to positive-trace regular-carrier identities.  A
future finite compiler must encode the norm-square standard-polynomial
instructions directly, rather than encode the prefix-isometry proof used only
for exact completeness.
