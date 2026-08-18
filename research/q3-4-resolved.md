---
rg: 2
id: q3-4-resolved
kind: claim
title: "Pestov Question 3.4 resolved either way: decide whether every hyperlinear group is sofic"
distinct_from:
  hyperlinear-nonsofic-group: that claim is one specific answer (the separation); this is the question itself, which is also resolved by proving the opposite answer hyperlinear-implies-sofic
  hyperlinear-implies-sofic: that claim is the affirmative answer; this is the question, established by either answer
root: true
---

A root question of the program, stated as the question rather than one of
its answers:
determine whether every hyperlinear group is sofic (Pestov, Question 3.4).
Exactly two routes can establish this claim, one per answer:

- **No** — `hyperlinear-nonsofic-group`: exhibit a hyperlinear group that is
  not sofic (the separation).
- **Yes** — `hyperlinear-implies-sofic`: prove that hyperlinearity implies
  soficity for groups.

Either answer is a landmark, and the two payoffs converge on this program's
targets: "no" is the separation itself, while "yes" combined with the
unconditional nonsofic groups (kun-thom-nonsofic-wreath) immediately yields an
explicit non-hyperlinear group — the other root target (non-hyperlinear-group).
So resolving Q3.4 in *either* direction closes a root of this graph.

(`goal: true` moved to `non-hyperlinear-group` on 2026-08-18: the program
keeps one goal, chosen for impact — the group-level Connes embedding
problem.  Nothing here changes in wiring: both answer routes stand, the
"no" side closes this root, and the "yes" side both closes it and feeds
the goal through `non-hyperlinear-from-hyperlinear-implies-sofic`.)

**Graph discipline.** As a bare disjunction "(∃ hyperlinear nonsofic group) ∨
(hyperlinear ⟹ sofic)" this statement is a classical tautology; its content is
knowing *which* disjunct holds. Therefore no `requires: []` direct route may
ever be written for this claim — only the two answer routes above are
admissible, and each becomes complete exactly when its answer is established.

**Asymmetry caveat.** The two sides are not equally actionable. Per
docs/OBSTRUCTIONS.md §5, candidate-by-candidate evidence that specific groups
fail hyperlinearity can never accumulate to the "yes" side; that side needs a
general conversion of hyperlinear approximations into sofic ones, for which no
technique exists, and it is at least as strong as exhibiting a non-hyperlinear
group. The "no" side is where all current routes in this graph live. This node
records what counts as success, not a judgment that both directions are
equally tractable.

**Status as of 2026-08-16 (external full-corpus audit, re-checked against live
`main`).** Still open, both sides. The audit found nothing in the corpus or
the literature bridging either gap, and the source of the nonsoficity theorem
still states in terms that it does not determine hyperlinearity of
`L_{F₂}(1,2)^×`. Two things moved, both on the Leavitt lane and neither
selecting a branch: `atlas-stabilizer-commutant-no-go` closes the campaign's
designated first search stage at every multiplicity, and
`atlas-defect-gap-limit` shows the criterion's defect minimum converges, so no
witness can hide at an isolated multiplicity. The audit also confirmed that two
snapshot-era worries are already discharged on live `main` — the rank-five
Steinberg completeness gap (`atlas-steinberg-spare-index-independence`) and the
last Lean `sorry` (closed at `1da7fd1f`; the tree now has none). Details in
`research/artifacts/hyperlinear-q34-audit-2026-08-16.md`. One logical reminder
the audit restates correctly: even a proof that the Leavitt candidate is
*non*hyperlinear — a landmark, since no nonhyperlinear discrete group is known
— resolves neither side of this goal. It selects `leavitt-steinberg-hs-stable`,
whose payoff is `non-hyperlinear-group`, a different root.
