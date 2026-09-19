---
rg: 2
id: s3-packet-projective-neutrality-proof
kind: route
title: Cancel the finite packet multiplier, induce over the type orbit, and cut back to the active fibre
target: s3-packet-dressing-preserves-projective-microstate-gap
requires:
  - finite-central-hs-sector-decomposition
  - deligne-sector-gap-is-exactly-nonhyperlinearity
  - thom-kazhdan-central-fibre-hyperlinear-nonamenable
---

Let `W_omega` be a nonzero finite-dimensional
`omega^(-1)`-projective representation of the finite group `H`.  Such a
module always exists: take the required central-character block of the left
regular representation of the finite Schur extension determined by `omega`.

If `U_n` is an `alpha^(-1)`-projective almost representation of `K`, then

```text
(h,k) |-> W_omega(h) tensor U_n(k)                         (SPP1)
```

is a `beta^(-1)`-projective almost representation of `H x K`.  Its relator
energy is bounded by a fixed multiple of that of `U_n`.  Inducing `(SPP1)`
from `H x K` to `F x K` supplies one fibre for every element of `O=F/H`.
The finite packet implementers cancel the remaining cocycle, so this is a
full packet-cell almost representation.  Every orbit fibre has the same
dimension; in particular the `sigma` fibre has density `1/|O|`.  Adding a
fixed finite multiplicity module changes that density only by a fixed
positive packet constant.

Conversely, compress a full packet-cell microstate to its `sigma` fibre after
the standard fixed finite-packet correction.  This gives a
`beta^(-1)`-projective active-stabilizer microstate, with only a fixed-factor
increase in normalized squared defect.  Restriction to `{1} x K` removes
`omega` and leaves an `alpha^(-1)`-projective microstate of `K`.  These two
operations prove the microstate equivalence.  The same estimates in both
directions show that the two all-dimensional defect infima vanish
simultaneously; if either is positive, the other is positive up to fixed
packet constants.

For the quantitative sector statement, first round the finite packet and
the central order-three word.  Fixed finite relations make the total
normalized-HS change `O(sqrt(E))`, and the squared relator energy of the
corrected tuple is at most `C_packet E`.  By
`finite-central-hs-sector-decomposition`, this tuple is an orthogonal sum of
central-character blocks and squared HS energies add with dimension weights.
If the chosen nontrivial block has normalized mass `q_nontriv`, its normalized
projective energy is at least `c^2`.  Therefore

```text
C_packet E
 >= q_nontriv c^2,                                        (SPP2)
```

which is `(SPD4)`.  A selected projection supported in that block has trace
at most `q_nontriv`; undoing the correction perturbs its trace by at most a
fixed multiple of `sqrt(E)`.  This proves `(SPD5)`.

For Thom's Kazhdan group, the LEF-window regular microstates retain every
nontrivial central character with positive asymptotic mass.  Applying
`(SPP1)` and finite-orbit induction gives the asserted positive-density
packet countermodels.  For Deligne's cover, the nontrivial character block is
the mod-three Maslov twisted sector.  `deligne-sector-gap-is-exactly-nonhyperlinearity`
states that its all-dimensional gap is equivalent to non-hyperlinearity of
`E_3`.  Thus the finite packet construction is neutral in both examples: it
neither defeats Thom's regular absorption nor proves Deligne's missing gap.
