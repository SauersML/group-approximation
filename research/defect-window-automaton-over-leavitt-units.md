---
rg: 2
id: defect-window-automaton-over-leavitt-units
kind: claim
title: Some injective automaton over the Leavitt unit group has a Garden of Eden on a compression-defect window
distinct_from:
  leavitt-units-carry-injective-invariant-output-automaton: that asks for an output constant on cosets of a finite subgroup, where the Garden of Eden is automatic; this asks for an arbitrary injective automaton whose Garden-of-Eden window is the pair {1, d} for a commutator d of the nonsoficity configuration.
  strict-automaton-tables-present-an-invisible-window-difference: that is the established necessary condition that some window difference is sofic-invisible in the table group; this is an open construction problem that places the window on the one element the compression mechanism is known to make invisible.
  nested-rigid-defects-force-nonsurjunctivity: that asks that a nested defect configuration force strictness in every group carrying it; this asks for one explicit automaton over the Leavitt units whose Garden-of-Eden window is a defect pair.
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
- *Where a small core dies.* Suppose the needed coincidences impose on the
  configuration letters only one compression relator `u l u^-1 = l'` and one
  commutation `[c, l] = 1`, and every other relator peels with a private generator
  (`forward-relations-of-a-counterexample-have-a-nonsofic-core`). With formal
  letters the relators themselves peel, so the group is free. Even with the S- and
  M-letters of `u, l, c` identified, eliminating `l'` gives
  `<u> * <l, c | [l, c]> = Z * Z^2`. In that group `d` is the reduced alternating
  word `u c u^-1 . l . u c^-1 u^-1 . l^-1`, hence nontrivial, and the group is
  residually finite. So `d` survives in a finite quotient, contradicting the
  required invisibility, and no such design has this window. The forward
  partition must force enough to kill `d` in every sofic quotient. Within current knowledge that means the whole criterion
  (`openai-expander-matching-criterion`): a presentation giving property (T) to
  the `Gamma`-letters and the ambient letters, the nesting relators, and a non-LEF
  presentation for the `J`-letters. No rule pair is known whose forward
  sufficiency needs a Kazhdan presentation. This is where the attempt dies today.
- *Forcing is not the bottleneck (gk-n-twocycle, 2026-09-12).* By
  `bijective-designs-force-every-finite-presentation`, shift–shear rule pairs force
  any finite presentation as a principal forward table, with one independent cycle per
  relator. That includes the whole criterion above, nesting relators too. Those pairs
  are bijective over every group, and composing a design with them never changes its
  strictness. So the death point just recorded is resolved, but only by pairs that
  give nothing. A rule pair for this claim must force the configuration through its
  irreversible part, and keep a reverse hinge word nontrivial in the forced core.
- *The Kun--Thom screen.* By `surjunctive-groups-carry-invisible-rigid-defects`, the
  surjunctive Kun--Thom wreaths already carry a nontrivial sofic-invisible rigid defect
  with the whole configuration present: a Kazhdan pair, a strict compressor and a
  centralizing involution. So the configuration relations never suffice, and a table
  for this claim must force a coincidence that fails in every such wreath. Nesting the
  conjugated centralizing element inside the compressed subgroup is the candidate
  distinction (`nested-rigid-defects-force-nonsurjunctivity`).
- *The presentation form of the problem, and the abelian layer.* Eliminating the
  decoder letters (`table-groups-are-memory-holonomy-groups`) turns the design problem
  into a question about presentations alone: find generators `x_m`, `m in M \ {1}`, and
  relators each of which is a product of edge labels -- a difference
  `x_(m') x_m^(-1)` for a balanced identification, a single letter for an anchored one --
  such that the difference `d = x_(m_1) x_(m_2)^(-1)` is nontrivial and sofic-invisible,
  and some reverse hinge survives. Two filters follow from the abelianization of that
  presentation (`table-hosts-have-a-cell-count-betti-lower-bound`,
  `two-cell-window-differences-die-in-host-abelianization`). The table must carry at
  least `|S| + |M| - 2` independent coincidences for a Kazhdan or simple host, and it
  must be anchored: an unanchored table gives `Z * Q`, whose Kazhdan subgroups are all
  conjugate into `Q`. Neither filter touches this window. The lattice test is vacuous on
  a commutator, and `d = [u c u^(-1), l]` is one, so the abelian layer screens
  single-letter windows and says nothing here. The attempt still dies at the same step.
- *Re-aimed at the hinge: the window lies in every hinge closure, and the defect is a
  transposed hinge.*
  - By `garden-of-eden-windows-fold-modulo-every-hinge-closure`, the window `{1, d}` forces
    `d` into the normal closure of the hinge words of every minimal reverse-sufficient
    partition of the pair's table group. The reverse hinges must normally generate the
    defect: inside its own tables the design must do to `d` what soficity does.
  - By `transposed-hinges-are-conjugated-commutators`, transposing a forward identification
    `(s,m) ~ (s',m')` leaves the hinge `s'^(-1) [m'^(-1) m, s m] s'`. For the rooted
    identification `(u c^(-1) u^(-1) l^(-1), l) ~ (1, u c^(-1) u^(-1))` it is exactly `d`.
  - So the most direct rule pair forces that identification, and every minimal reverse
    partition needs its transpose. Such a pair is strict over every realization in which
    its forward partition holds and `d != 1`, the Leavitt unit group included. It would
    refute Gottschalk even with its Garden of Eden on some other window.
  - It dies at the rules: no rule pair is known whose reverse sufficiency needs the
    transpose of an identification its forward sufficiency needs. The transpose always
    suffices when `S = {1}` or `M = {1}`
    (`boolean-core-is-uniform-single-demand-network-coding`). The rooted identification
    holds over the free group on the memory letters, so by
    `free-memory-injectivity-forces-universal-bijectivity` the pair must also need cycle
    relators that fail in every surjunctive cover of its memory group, the nesting relator
    for instance.
