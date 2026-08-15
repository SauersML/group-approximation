---
rg: 2
id: q3-4-resolved
kind: claim
title: "Pestov Question 3.4 resolved either way: decide whether every hyperlinear group is sofic"
distinct_from:
  hyperlinear-nonsofic-group: that claim is one specific answer (the separation); this is the question itself, which is also resolved by proving the opposite answer hyperlinear-implies-sofic
  hyperlinear-implies-sofic: that claim is the affirmative answer; this is the question, established by either answer
root: true
goal: true
---

The program goal, stated as the question rather than one of its answers:
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
