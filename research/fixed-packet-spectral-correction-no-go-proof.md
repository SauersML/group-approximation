---
rg: 2
id: fixed-packet-spectral-correction-no-go-proof
kind: route
title: Apply the spectral-gap dichotomy on the arbitrary packet multiplicity algebra
target: fixed-packet-spectral-correction-is-gap-or-regular-collapse
requires: []
---

After exactifying the fixed finite group, an isotypic packet corner is
`M_r(C) tensor M_m(C)` with arbitrary `m`.  A hard spectral cut needs uniform
control of the multiplicity mass in shrinking threshold windows: otherwise
move the operator across the threshold on the positive-density near-threshold
summand.  This changes the operator by arbitrarily little in normalized HS
norm while the cut stays a fixed distance apart.  Such spectral-mass control
is an additional coercivity theorem, not a consequence of the finite packet.
If it is obtained through estimates valid in arbitrary finite tracial
algebras, a continuous ramp differs from the cut in squared L2 norm by at
most the threshold-window mass.  Uniform polynomial approximation of that
ramp and fixed-word telescoping then put the cut in the functorial
fixed-packet calculus of
`fixed-packet-julia-calculus-is-tracially-functorial` and extends to every
finite tracial multiplicity algebra.

At zero defect in the regular finite factor, `(FSC2)` gives a conjugate
subprojection.  The Halmos specialization of
`universal-block-return-violates-the-regular-firewall` forces equality and
kills its exit.  Any functorial support of a marked involution on that exit
therefore kills the group element itself.

Finally a fixed nonzero polynomial cannot vanish on `M_m(C)` for arbitrary
`m`: evaluate its variables as truncated left shifts on words up to its
degree.  Thus fixed polynomial identities either fail at some
multiplicity or are universal algebraic identities and belong to the same
regular-factor calculus.  These alternatives prove the claim.
