---
rg: 2
id: zaremsky-2-17-t-contains-t-times-t
kind: claim
title: "Zaremsky Problem 2.17 resolved: does Thompson's group T contain a copy of T x T?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 17,
verbatim: "(Added 2/10/24) Does `T` contain a copy of `T × T`? (Surely yes,
but how?) [In fact no! Jim Belk points out that every finite subgroup of `T`
is cyclic, so `T` cannot contain `T × T`.]"

This claim is the question. It is established only through an answer route:

- **No**: `zaremsky-2-17-by-no` requires
  `thompson-t-has-no-subgroup-isomorphic-to-t-times-t`.
- **Yes** would be a subgroup of `T` isomorphic to `T × T`. The no answer
  refutes it, so no yes-route is written.

Never write a `requires: []` route into this claim.

**Reading.** "A copy of `T × T`" means a subgroup of `T` isomorphic to
`T × T`, that is, an injective homomorphism `T × T → T`.

**Status.** Answered negatively in the list's own note, from an observation of
Jim Belk.
