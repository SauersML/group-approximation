---
rg: 2
id: fanizza-boone-mark-carrier-interface
kind: claim
title: Feed a surviving Boone word into the initial Fanizza child carrier with constant HS loss
artifacts:
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
distinct_from:
  fanizza-nonmember-signal-is-not-a-separated-mark: that proves the published projection D cannot itself fill this role; this asks for the missing positive construction with a separate word.
  boone-commutator-criterion-for-halting: that is an exact word-equality criterion; this asks for a normalized-HS quantitative coupling from separation of that word to positive initial carrier mass.
---

Extend the Fanizza machine BCS/groupification by a Boone or self-referential
word `w_M` such that:

1. if `M` does not halt, `w_M!=1` in the resulting finitely presented group;
2. for every normalized-HS microstate in which
   `||w_M(U)-I||_2>=alpha`, a fixed initial child projection in the Fanizza
   recurrence has trace at least `c(alpha)>0`, up to an error bounded by a
   machine-independent multiple of the group-relator defect;
3. if `M` halts, the published Fanizza signal collapse and the groupification
   relations drive the same carrier to zero with total constant independent of
   runtime.

## Attempts

- **Set the mark equal to `D`: invalid.**  On the nonmember side every perfect
  strategy has `phi(D)=0`, by
  `fanizza-nonmember-signal-is-not-a-separated-mark`.
- **Use a long van Kampen equality from the Boone word to `D`: insufficient.**
  Its area can grow with runtime and destroys the uniform normalized-HS
  constant.
- **Live attack.**  Use a conjugacy-compressed terminal flag so its relator norm
  is runtime-independent, then couple its spectral carrier to the level-zero
  Fanizza projection by one fixed packet relation.  The missing estimate is the
  uniform semantic comparison, not the norm of the conjugate flag itself.
