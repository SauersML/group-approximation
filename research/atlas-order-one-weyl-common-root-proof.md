---
rg: 2
id: atlas-order-one-weyl-common-root-proof
kind: route
title: Evaluate the three-label packet in rational rotation traces
target: atlas-order-one-weyl-atlas-is-one-laurent-common-root-test
requires:
  - atlas-three-label-mode-two-unitary-moment-reduction
  - leavitt-regular-atlas-block-monomial-gap
---

For coprime `p_n,q_n`, the standard `q_n`-dimensional clock and shift pair
with phase `z_n` is irreducible, so it generates `M_(q_n)(C)`.  Commuting
letters to normal form gives `(OWA3)`.  Because every word `M_s(i,j)` has
fixed length while `q_n->infinity`, its normalized trace is eventually zero
unless the two integer exponent sums `a,b` both vanish.  In the balanced
case its trace is `z_n^Area`.  Substitution in `(TLM7)` and passage to the
limit gives `(OWA4)`--`(OWA5)`.

The same moment formula is the canonical trace formula for the rotation
algebra `A_z`: its trace vanishes on `u^a v^b` unless `a=b=0`.  This proves
the equivalence with item 3.  Since a unitary in a finite tracial von Neumann
algebra has trace one only when it is the identity, `Re f_s(z)=1` is
equivalent to `f_s(z)=1` and to exact satisfaction in that GNS
representation.

The preceding limit computation uses only `q_n->infinity`, so it remains
valid when the limit `z` is a root of unity.  It must not be replaced in that
case by one fixed irreducible Weyl representation: exponent sums which are
nonzero integers but divisible by the fixed order then survive the trace,
whereas they vanish eventually along `(OWA1)`.  Thus finite-dimensional
invisibility supplies no torsion-root exclusion.  The case `z=1` is excluded
by the established small-phase commutative wall.  Finally `(OWA6)` follows
directly from `S_nD_n=z_nD_nS_n`, and all its singular values equal
`|z_n-1|`.
