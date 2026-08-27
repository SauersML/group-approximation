---
rg: 2
id: pzk-tableau-gap-full-corner-monomial-realization
kind: claim
title: Complete the rational separated PZK tableau to a full-corner monomial matrix pair
artifacts:
  - research/artifacts/mastel-slofstra-tableau-compiler-audit-2026-08-23.md
distinct_from:
  bisynchronous-to-monomial-game-algebra-compiler: that starts with the Harris completion of an arbitrary fixed separated synchronous game; this starts with the narrower private-S5-word tableau and its equal-marginal answer-split trace.
  smooth-label-cover-gap-full-corner-monomial-realization: that starts with edge-dependent projection-color maps; this starts with shared Boolean shares and private randomizing-tableau word equations.
  pzk-tableau-private-s5-gauge-normal-form: that proves only the source normal form and trace profile; this must preserve the full universal tracial and Connes-embeddable representation spaces.
---

**OPEN.**  For `B_tab` from
`lin-pzk-tableau-rational-qc-not-qa-correlation`, construct a finite phase
order `s` and finite matrices `A,B` whose `s`-monomial quantum-isomorphism
algebra is *-isomorphic to the synchronous tableau algebra, or contains it as
an explicitly full corner preserving both

```text
nonzero tracial representations, and
nonzero homomorphisms into R^omega.                      (PTM1)
```

The allowed source may be the equal-marginal answer-splitting refinement.
The input is narrower than a generic BCS: every `S5` gauge variable is
private, the gauge updates and final row check are reversible group word
equations, and only five-share Boolean bits cross original contexts.

What remains is operator-algebraic rather than probabilistic.  Equal trace of
the selected answer PVMs does not supply the column partitions of one square
quantum-reflection matrix.  The Boolean-to-instruction lookup is not a
general `S5` word equation, and auxiliary incidence blocks can introduce new
`R^omega` representations unless their corner is proved full.  Realizing
only the rational perfect correlation does not establish `(PTM1)`.
