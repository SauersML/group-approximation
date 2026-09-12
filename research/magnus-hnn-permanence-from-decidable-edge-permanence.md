---
rg: 2
id: magnus-hnn-permanence-from-decidable-edge-permanence
kind: route
title: Magnus edges have decidable membership, so the general decidable-edge permanence covers them
target: bh-embeddability-survives-magnus-subgroup-hnn
requires: [bh-embeddability-survives-decidable-edge-hnn, magnus-moldavanskii-hierarchy-with-decidable-edges]
---

Take `H = <Y | s>`, `Y_1`, `Y_2` and `β` as in
`bh-embeddability-survives-magnus-subgroup-hnn`. Check the hypotheses of
`bh-embeddability-survives-decidable-edge-hnn` with `A = H`,
`C_i = <Y_i>` and `phi = β`:

- **`A` finitely generated,** by the finite set `Y`, and it embeds in a
  finitely presented simple group by assumption.
- **`C_1`, `C_2` finitely generated,** by the finite sets `Y_1`, `Y_2`.
- **Decidable membership.** Membership in `C_i` is decidable in `H` by item 2 of
  `magnus-moldavanskii-hierarchy-with-decidable-edges`, Magnus's solution of the
  generalized word problem.
- **Computable isomorphism.** `β` is given on generators, and it is an
  isomorphism `C_1 -> C_2` by item 1 (the Freiheitssatz), since each `Y_i` omits
  a letter of `s`.

Hence `H*_β` embeds in a finitely presented simple group. `∎`
