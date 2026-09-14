---
rg: 2
id: reduced-lots-have-concatenable-tietze-presentations
kind: claim
title: Every reduced LOT group has a Tietze presentation whose relators but one have concatenable minima
distinct_from:
  lot-groups-are-torsion-free: that asks only for torsion-freeness; this asks for an explicit presentation meeting the Barreto--Minian criterion, which gives local indicability and asphericity as well.
  crossing-pair-two-cycle-lot-groups-are-locally-indicable: that proves this for LOTs whose left graph has cyclomatic number two and a separated crossing pair, with one elimination; this asks it for every reduced LOT.
  labeled-oriented-trees-are-aspherical: that is asphericity of all LOT complexes; this is a stronger, presentation-level statement that implies it through local indicability.
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
  - research/artifacts/hl-whitehead-lot-certify-2026-09-14.md
---

**OPEN.** For every compressed, interior reduced and boundary reduced LOT `Γ`, some sequence of
eliminations gives a presentation of `G(Γ)` satisfying the hypothesis of
`barreto-minian-concatenable-minima-give-local-indicability`, with the multisets of minima of all
relators but one concatenable. Each elimination removes a generator that occurs once in a relator,
together with that relator. The resulting presentation keeps deficiency `1`, `H_1 = Z` and total
exponent `0`.

**Why it matters.** It implies local indicability of every LOT group, hence
`lot-groups-are-torsion-free` (route `lot-torsion-free-via-concatenable-tietze-presentations`) and
asphericity of every LOT complex (`locally-indicable-2-complex-with-h2-zero-is-aspherical`).
Barreto--Minian say local indicability of LOT groups is open.

**Evidence, not proof.**
- With no elimination, it holds when `T(Γ)` or `I(Γ)` has at most one cycle (Barreto--Minian,
  Corollary 3.1).
- With one elimination, it holds for the class of `crossing-pair-two-cycle-lot-groups-are-locally-indicable`.
- The seven-vertex census (`research/artifacts/hl-whitehead-lot-certify-2026-09-14.md`, Section 3)
  certified the 13 hardest classes by breadth-first eliminations followed by Theorem 2.5, each within two
  eliminations.
- The census certified the other classes by several tests, not all of them Theorem 2.5, so it is not
  full evidence for this statement.

**Candidate counterexamples.** LOTs with no crossing pair and both graphs of cyclomatic number at least
`3`. After a first elimination the labels become words, so the exact minima computation of
`crossing-pair-two-cycle-lot-li-proof` no longer applies as it stands.
