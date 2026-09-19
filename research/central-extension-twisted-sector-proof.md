---
rg: 2
id: central-extension-twisted-sector-proof
kind: route
title: Cut by the central spectral projection, and direct-sum back
target: central-extension-twisted-sector-criterion
requires: []
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
  - notes/NOTEPAD.md
---

## Direct proof

Provenance: `notes/NOTEPAD.md:39199-39232` (2026-08-10), recorded there for a
different candidate and never applied to the marked quotients.  Both
directions were re-derived in Section 10 of the cited note.

*Necessity.*  An injective corona representation `Theta` of `G` has
`Theta(z) != 1` for the central generator, and `Theta(z)^2 = 1`, so the
spectral projection at `-1` is a nonzero projection commuting with
`Theta(G)`.  Cutting by it gives a corona representation with
`Theta(z) = -1`; its values on a section satisfy the twisted relation.

*Sufficiency.*  Given `v_n` and a faithful MF model `pi` of `K`, put
`V_n(s(k)c) = chi(c) v_n(k) (+) pi_n(k)`.  Block-diagonal multiplicativity is
the cocycle identity, the second block separates elements with nontrivial
image in `K`, and the first separates the central generator, since
`chi(z) = -1`.

Stated for order two, which is the case used here; for a cyclic kernel of
prime order `p` the same argument gives the equivalence for some nontrivial
character, and fixing the character in advance needs an extra step not
verified here.
