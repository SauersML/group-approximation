---
rg: 2
id: leavitt-24k-blockwise-normalizer-exclusion-proof
kind: route
title: Bound the bad-block weight, collapse the 3-cycle on a good block, and read off the surviving commutator
target: leavitt-24k-models-avoid-blockwise-error-basis-normalizers
requires:
  - error-basis-normalizer-has-a-sharp-trace-gap
  - mf-obstruction-gives-a-finite-c-killing-relation-set
  - leavitt-24k-first-relation-has-exact-finite-model
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

Section 5 of the artifact. Fix a comparison tuple `Y` in the class and
let `delta` be the largest generator displacement. Word continuity gives
`||r(Y)-I||_2 <= epsilon + L delta` for every `r in S`, with the
`epsilon` term absent on the internal relators, which `X` satisfies
exactly.

Call a block bad when some `r in S` is nonscalar on it. Block
restrictions of `Y` lie in the block normalizer, a group, so the first
prerequisite gives each nonscalar restriction squared distance at least
`gamma^2` inside its block. Additivity of the unnormalized trace across
orthogonal blocks turns this into a bound on the bad-block weight,
`beta <= M (epsilon + L delta)^2 / gamma^2`.

On a good block every word of `S` is scalar, so the four restrictions
descend to the finite group `N(W_j)/T I`, satisfy all internal relations
of `P`, and kill `T`. The second prerequisite makes the image of the
3-cycle trivial, so `Y_c` is scalar there and the length-eight word
`d = [b_2, c b_1 c^-1]` collapses to `[Y_2, Y_1]`. That commutator is
exactly the identity for `X`, so it is within `4 delta` of the identity
globally; bad blocks contribute at most `4` each. Combining and using
`sqrt(x+y) <= sqrt x + sqrt y` bounds `||d(X)-I||_2` above by
`12 delta + (2 sqrt M/gamma)(epsilon + L delta)`.

The third prerequisite supplies the matching lower bound: its necessary
bound `(LR2)` says `||d(X)-I||_2 >= (sqrt 2 - epsilon)/2` whenever
`tr_D(C^2) = 0`, because `z`, `b` and `d` are free-group conjugates
and `||C^2-I||_2 = sqrt 2`. That bound is consumed here rather than
reproved; note `c^-1 d c = c^2 d c^-2`, so the two spellings of the word
agree. Putting the two inequalities together is the displayed estimate,
and taking the infimum over comparison tuples replaces `delta` by
`delta(X)`.

Scalar phases are handled rather than assumed away: a word scalar on a
block need not be the identity there, and it is the exact commutation of
`B_1, B_2` that keeps the surviving commutator out of those phases. A
block chosen from a trace-zero generator alone would not give this.
