---
rg: 2
id: sampled-character-hash-closes-multicharacter-alignment
kind: route
title: Hash terminal characters and align the sampled coordinate PVM
target: multicharacter-pvm-alignment-modulo-simultaneous-gauge
requires:
  - weighted-code-character-hash
  - two-code-character-cut-recenters-to-one-coordinate
  - sampled-coordinate-joint-pvm-tracks-terminal-character-hash
---

Choose a target collision tail `eta->0` and then a slowly growing hash length
`t=O(log(1/eta))` for which `t epsilon->0` and the finite-family commuting
correction error also tends to zero.  The random hash lemma simultaneously
selects rows of total complete-pair cost `O(t epsilon)` and leaves at most
`eta` of the weighted distinct-character boundary unresolved.  The sampled
joint-PVM theorem transports the terminal hash to a genuine common PVM
modulo one gauge.  Pinching by it costs the sampled row energy plus the
unresolved collision tail and terminal diagonal error, all `o(1)`.  Merge
equal hash sectors and then equal character sectors.  This proves `(MCA1)`.
