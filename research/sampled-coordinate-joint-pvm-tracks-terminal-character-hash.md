---
rg: 2
id: sampled-coordinate-joint-pvm-tracks-terminal-character-hash
kind: claim
title: A slowly growing sampled-coordinate joint PVM tracks the terminal character hash modulo gauge
distinct_from:
  weighted-code-character-hash: that selects coordinates with small unresolved block mass and row energy; this must construct the actual gauge-aligned joint PVM from their raw approximate reflections
  two-code-character-cut-recenters-to-one-coordinate: that handles one sampled reflection exactly; this must align a slowly growing family simultaneously
  multicharacter-pvm-alignment-modulo-simultaneous-gauge: that asks for the final all-character pinching estimate; this is the sampled-hash realization step intended to prove it
---

OPEN.  In the setting of
`multicharacter-pvm-alignment-modulo-simultaneous-gauge`, select
`t=t(epsilon)->infinity` coordinates using
`weighted-code-character-hash`, slowly
enough that `t epsilon->0` and fixed-`t` normalized-HS stability can correct
the sampled raw reflections to commuting reflections.

Prove that their joint PVM may be chosen, modulo one simultaneous unitary
gauge, to implement the corresponding coordinate hash of the terminal
character atoms up to `o(1)` weighted off-diagonal generator mass.
Equivalently, after merging terminal atoms with the same sampled sign vector,
the corrected sample PVM must have a matching whose transported block
pinching differs by `o(1)` in the averaged generator metric.

Once this matching is obtained, `(RCH1)` leaves `o(1)` unresolved
distinct-character boundary, `(RCH2)` makes the sampled PVM boundary
`O(t epsilon)=o(1)`, and same-hash atoms may be merged.  The statement is a
multi-reflection CS/inertia theorem: small pair commutators alone correct the
sample algebra, but one must also show that the correction chooses the
terminal character multiplicities rather than an unrelated nearby joint
spectrum.

## Attempts

1. **Correct sampled reflections abstractly.**  Fixed-family HS stability
   gives some commuting tuple, but does not by itself identify its joint
   spectral multiplicities with the signs obtained by compressing against
   the terminal PVM.
2. **Match one coordinate at a time.**  The two-character spectral
   recentering theorem supplies the one-coordinate CS matching.  Iterating
   arbitrary matchings can change the earlier spectral cuts; a simultaneous
   Hall/transport or polar-intertwiner argument is needed.
3. **Demand exact separation of all labels.**  This recreates the
   `log |D|` firewall.  The random hash lemma shows only weighted matching is
   necessary, with `t` depending on the target error rather than `|D|`.
