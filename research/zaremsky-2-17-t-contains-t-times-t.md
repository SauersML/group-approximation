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

## Attempts

1. **Torsion-free strengthening (wave flagship-2026-09-17, lane sw-119).**
   Belk's torsion argument does not rule out `T × Z` or `T × F` inside `T`.
   `thompson-t-contains-no-t-times-g` rules out `T × G` for every nontrivial
   `G`. The proof goes through `thompson-t-copies-of-t-have-trivial-centralizer`:
   an element of `T` commuting with a copy of `T` either has a fixed point, and
   then its support must cost infinitely many breakpoints
   (`thompson-t-centralizers-of-orbit-free-subgroups-act-freely`), or it has
   nonzero rotation number, and then either a torsion clash or a descent to
   rotations gives a contradiction. The answer "no" to Problem 2.17 therefore
   does not depend on torsion at all.
