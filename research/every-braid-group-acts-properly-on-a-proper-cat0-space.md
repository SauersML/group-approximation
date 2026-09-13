---
rg: 2
id: every-braid-group-acts-properly-on-a-proper-cat0-space
kind: claim
title: Every braid group acts properly by isometries on a proper CAT(0) space
distinct_from:
  every-braid-group-is-cat0: that claim asks for a geometric (proper and cocompact) action; this one drops cocompactness and keeps the space proper
---

For every `n >= 1` there is a proper (complete and locally compact) CAT(0)
metric space on which `B_n` acts properly by isometries. "Properly" is meant as
in Bridson–Haefliger: every point has a ball whose translates meet it for only
finitely many group elements.

This is the reading of Zaremsky's second sentence in Problem 3.6 ("Even
without requiring cocompactness this is unknown") that stays in the setting of
CAT(0) groups. Two nearby readings change the question:

- if the space need only be complete, Hilbert spaces count, and a proper
  affine isometric action on a Hilbert space, i.e. the Haagerup property
  (`every-braid-group-has-the-haagerup-property`, Problem 3.7), would be
  enough;
- if the space need not be complete, Weil–Petersson Teichmüller space is a
  candidate, and a finite-index subgroup of `B_n` acts on it properly; its
  completion is CAT(0), but the action on the completion has infinite point
  stabilizers (sources to verify).

Known: true for `n <= 6`, because a geometric action is a proper action on a
proper space (routes `braid-proper-cat0-action-from-geometric-action` and
`braid-groups-on-at-most-six-strands-are-cat0`; `n = 7` per Jeong's preprint).

## Attempts

- **Number-field linearity (lane z3-02-braid-glnz).** Route
  `braid-proper-cat0-action-via-number-field-linearity`: a finitely generated
  subgroup of `GL_m(F)`, `F` a number field, is discrete in a finite product of
  local groups and acts properly on a product of symmetric spaces and
  Bruhat–Tits buildings, a proper CAT(0) space
  (`number-field-linear-groups-act-properly-on-cat0-spaces`). So
  number-field linearity of `B_n` (hence a yes to Problem 3.2) would give this
  claim, and a no here refutes Problem 3.2.
- **Lawrence–Krammer linearity is not enough as it stands.** `B_n` embeds in
  `GL_m(Z[q^{±1}, t^{±1}])` (Bigelow, Krammer). This lane's sketch: that group
  acts metrically properly on an ℓ²-product of the four Bruhat–Tits buildings of
  the valuations `v_q, v_{1/q}, v_t, v_{1/t}` (residue fields `Q(t)` or `Q(q)`,
  so not locally finite), a Euclidean plane for `det`, and a weighted infinite
  ℓ²-product of symmetric spaces `GL_m(C)/U(m)` at a dense sequence of
  specializations. The result is complete but not locally compact, so it answers
  only the complete-space reading; not yet written up as its own node.
- Without cocompactness, isometries need not be semisimple, so the
  translation-length obstructions in `some-braid-group-is-not-cat0` do not
  apply to this claim.
