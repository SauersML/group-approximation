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

**Refutation shape.** A surjunctive group with a nested nontrivial rigid defect. It would
be nonsofic, by `sofic-groups-kill-rigid-compression-defects`.

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
- **Refutation through the permanence closure.** A surjunctive counterexample inside
  `S*` must avoid every finitely presented infinite simple nonsofic subgroup
  (`gottschalk-counterexamples-lie-outside-the-permanence-closure`). All the defect
  carriers checked so far exhibit only non-nested defects. Whether some group of `S*`
  carries a nested nontrivial rigid defect is open.
