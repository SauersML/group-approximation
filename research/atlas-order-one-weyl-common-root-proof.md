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
valid when the limit `z` is a root of unity.  In that case the universal
rotation algebra `A_z` is subhomogeneous with finite-dimensional fibers and
its canonical Fourier-coefficient trace is faithful (equivalently, use the
faithful conditional expectation onto one circle algebra followed by Haar
integration).  If all `f_s(z)=1`, the corresponding packet unitaries have
faithful trace one, hence are identities in `M_20160(A_z)`.  Composing with a
finite-dimensional fiber representation gives an exact regular-A8 atlas,
contradicting finite-dimensional invisibility.  This proves the torsion-root
exclusion.

It is essential not to substitute one fixed irreducible Weyl trace for the
canonical trace in this proof.  Exponent sums which are nonzero integers but
divisible by the fixed order survive in that fiber, whereas `(OWA4)` comes
from the center-integrated canonical trace and kills them.  Finally `(OWA6)`
follows directly from `S_nD_n=z_nD_nS_n`, and all its singular values equal
`|z_n-1|`.
