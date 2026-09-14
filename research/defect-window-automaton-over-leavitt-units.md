---
rg: 2
id: defect-window-automaton-over-leavitt-units
kind: claim
title: Some injective automaton over the Leavitt unit group has a Garden of Eden on a compression-defect window
distinct_from:
  leavitt-units-carry-injective-invariant-output-automaton: that asks for an output constant on cosets of a finite subgroup, where the Garden of Eden is automatic; this asks for an arbitrary injective automaton whose Garden-of-Eden window is the pair {1, d} for a commutator d of the nonsoficity configuration.
  strict-automaton-tables-present-an-invisible-window-difference: that is the established necessary condition that some window difference is sofic-invisible in the table group; this is an open construction problem that places the window on the one element the compression mechanism is known to make invisible.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

**OPEN.** Let `G = R^x`, `R = L_(F_2)(1,2)`, and take the nine-leaf configuration
`Gamma = EL_alpha(R)`, `J = V_(1000)`, compressor `u` of
`openai-nine-leaf-leavitt-configuration` (`u Gamma u^-1 <= Gamma`,
`[Gamma, J] = 1`, `u J u^-1 <= Gamma`). For `c in J`, `c != 1`, and `l in Gamma`
not commuting with `u c u^-1`, put `d = [u c u^-1, l] != 1`. Exhibit a finite
alphabet, an automaton `tau` over `G` with a left inverse `sigma`, and a Garden of
Eden for `tau` on the window `{1, d}`.

## Attempts

- *Admissible by counting.* `Rad(R^x) = R^x`
  (`leavitt-unit-group-has-only-trivial-sofic-morphisms`), so the window
  localization theorem allows a two-cell window on any nontrivial element, `d`
  included.
- *The rules must need the configuration.* By
  `strict-automata-live-on-canonical-table-groups`, strictness must already hold
  over the canonical table group `U_E` of a minimal forward partition. Relators
  that the decoder does not need never enter `U_E`, so adjoining the configuration
  as padding adds only free letters. By
  `strict-automaton-tables-present-an-invisible-window-difference`, the table
  group with the window products must kill `x_d` in every sofic quotient.
- *Where a small core dies.* Suppose the needed coincidences force only one
  compression relator `u l u^-1 = l'` and one commutation `[c, l] = 1` among the
  configuration letters. After eliminating `l'`, the core is
  `<u> * <l, c | [l, c]> = Z * Z^2`. That group is residually finite, and `d` is
  nontrivial in it, so `d` survives in a finite quotient and no such design can
  have this window. The forward partition must force enough to kill `d` in every
  sofic quotient. Within current knowledge that means the whole criterion
  (`openai-expander-matching-criterion`): a presentation giving property (T) to
  the `Gamma`-letters and the ambient letters, the nesting relators, and a non-LEF
  presentation for the `J`-letters. No rule pair is known whose forward
  sufficiency needs a Kazhdan presentation. This is where the attempt dies today.
