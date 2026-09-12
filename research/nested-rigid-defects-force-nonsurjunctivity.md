---
rg: 2
id: nested-rigid-defects-force-nonsurjunctivity
kind: claim
title: Every group carrying a nested nontrivial rigid compression defect is nonsurjunctive
distinct_from:
  leavitt-unit-group-nonsurjunctive: that asks for a strict automaton over one group; this asks that one exact configuration, present in that group, force strictness in every group.
  surjunctive-groups-carry-invisible-rigid-defects: that shows non-nested rigid defects occur in surjunctive groups; this is the open question whether nesting the conjugated commuting element inside the compressed Kazhdan subgroup changes the answer.
  sofic-groups-kill-rigid-compression-defects: that forbids any nontrivial rigid defect in a sofic group; this asks for the dynamical conclusion, nonsurjunctivity, from the nested case.
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

**OPEN.** Let `H` be countable, and let `Gamma <= G <= H` be a rigid pair: `Gamma` and
`G` Kazhdan, and `Gamma` infranormal in `G`. Suppose `t in G`, `z in C_H(Gamma)` and
`gamma in Gamma` satisfy

    t z t^-1 in Gamma,        [t z t^-1, gamma] != 1.

Then `H` carries an injective, nonsurjective cellular automaton on some finite-alphabet
full shift.

**Payoff.** `leavitt-units-carry-nested-rigid-defect` makes the binary Leavitt unit group
such an `H`, so this claim refutes Gottschalk's conjecture
(`nonsurjunctive-from-nested-rigid-defect`).

**Reduction.** By `nested-rigid-defects-live-in-nonsofic-kazhdan-groups`, `z` lies in
`G`. The defect is then one of the Kazhdan group `G` itself, which is nonsofic with
`C_G(Gamma)` not normal. So the claim is equivalent to its case `H = G`: every Kazhdan
group with an infranormal Kazhdan subgroup `Gamma` and a nested nontrivial defect is
nonsurjunctive.

**Refutation shape.** A surjunctive group containing a nonsofic Kazhdan group that has
a nested nontrivial rigid defect.

## Attempts

- **Counting along permutation models.** Vacuous. Rigid defects lie in the sofic radical
  (`surjunctive-groups-carry-invisible-rigid-defects`, part 1), so the
  Gromov--Weiss charts on `{1, d}` collapse at density one. Nothing distinguishes a
  strict automaton from a surjective one there.
- **Drop the nesting.** False. The Kun--Thom graph wreaths are surjunctive and carry
  nontrivial non-nested rigid defects (`surjunctive-groups-carry-invisible-rigid-defects`,
  part 2). Any proof must consume the relation `t z t^-1 in Gamma`.
- **Free commuting factors.** They give no strictness in either direction
  (`free-centralizer-amalgams-are-surjunctivity-inert`). The nesting must bind `z` to
  the host through the host's own relations.
- **Direct design on the window `{1, d}`.**
  - The overlap lemma (artifact Section 1) forces `d` into `M M^-1`.
  - By `strict-pairs-transfer-to-table-realizations`, the product tables must contain a
    coincidence that fails in every Kun--Thom graph wreath.
  - No local rule is known whose decoder identity reads the nesting relation.

  The attempt dies at constructing the left inverse. No candidate rule was found.
- **Refutation through the permanence closure.** A surjunctive counterexample must
  contain a nonsofic Kazhdan group with a nested defect
  (`nested-rigid-defects-live-in-nonsofic-kazhdan-groups`). Inside `S*` it must also
  avoid every finitely presented infinite simple nonsofic subgroup
  (`gottschalk-counterexamples-lie-outside-the-permanence-closure`). All the defect
  carriers checked so far exhibit only non-nested defects. It is open whether any known
  surjunctive nonsofic group contains a nonsofic Kazhdan subgroup at all. That is the
  first question for a refutation. For the Kun--Thom wreaths,
  `wreath-subgroups-meeting-lamps-finitely-are-rf` narrows it: such a subgroup must meet
  the lamp kernel in an infinite subgroup.
- **Choosing the group last.** Coarsening a reverse table can only help surjectivity
  (`strict-automata-live-on-canonical-table-groups`). So the nesting relation can matter
  only if the minimal forward-sufficient partition of some rule pair forces it. A proof
  of this claim must produce a rule pair whose canonical table group maps into the
  Kazhdan group with the nesting intact. None was found.
