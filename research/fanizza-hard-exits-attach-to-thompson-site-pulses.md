---
rg: 2
id: fanizza-hard-exits-attach-to-thompson-site-pulses
kind: claim
title: Attach every Fanizza hard exit to the corresponding Thompson site pulse
distinct_from:
  product-clock-synchronizes-fanizza-and-e5: that synchronizes the computation with an overlapping polynomial coefficient clock; this must attach the finite Fanizza packet menu to independent site-local doubled packets.
  packet-hard-transport-preserves-pulse-prefix: that asks an E5 hard word to preserve all earlier polynomial pulse signs; this uses off-site commutation to preserve the prefix by construction.
---

Put one independent Thompson pulse factor behind each member of the fixed
finite menu of source/target hard signs.  It is **not** necessary to identify
the level-`n` global Fanizza hard word `A_n` with the local source sign `a_n`.
By
`prefix-preserving-two-step-hard-bridge-localizes-exit`, it is enough to add a
unitary `u_n` satisfying

```text
a_nu_n=u_nA_n,               [u_n,B_k]=1  (k<n).       (FAT1)
```

The site swap `s_n` then sends `u_nP_n` into the fresh first-hit sector.
`product-clock-global-hard-bridge-has-finite-orbit` supplies all the bridges
from one prototype per menu role.  The product clock `Ug_r` advances the
global Fanizza word by `U` and its independent pulse site by `g_r`; the two
Thompson pair-orbits give every off-diagonal commutator.  All word lengths and
derivation areas are polynomial in the level.

The desired conclusion is that the analytically projected joint exit `P_n`
obeys `(PPB3)--(PPB4)` at every recurrence level.  Then `(PPB5)--(PPB6)` place
it in the summable first-hit sector `X_n`, removing
`e5-tail-character-suppression-for-projected-exits` from this route.

For a linear ordering of role/level pairs, compress each raw projected exit
by all earlier positive pulse cuts.  Since the pulse factors commute with the
source group, this gives a projection satisfying `(PPB3)`.  The removed mass
is already in an earlier first-hit sector.  Equations `(PGB6)--(PGB7)` give
`(PPB4)`, and therefore `(PPB5)--(PPB6)` put every remaining exit in a fresh
summable sector.

The exact marked-completeness clause follows from gauge doubling: each private
hard sign is spectrally balanced, so one base bridge can be chosen after
amplification and then transported by the product clock.  Shared logical BCS
words stay in the original factor.  Thus the construction neither copies them
into commuting lamp sites nor imposes relations among different bridges.

## Attempts

- A separate independent lamp pulse has the correct trace budget but needs a
  bridge from the literal packet hard sign.  Direct identification is
  stronger than necessary; `(FAT1)` is the exact minimal analytic interface.
- Identifying original BCS variables across all sites would add forbidden
  cross-context commutations.  Only private packet/frame words may be
  site-local; shared logical words must remain the existing recurrence words.
- The finite packet menu makes the number of local roles finite, but the
  active-return projection is analytic rather than a group word.  Its
  approximate reduction and placement must use the established packet
  complement estimates, not a universal projection relation.
- Infinite amplification and gauge covariance give the simultaneous exact
  bridges by `gauge-covariant-hard-shares-admit-site-bridges`; the product-clock
  compiler supplies the formerly missing finite presentation and polynomial
  approximate estimate without making the hard share site-local.
