---
rg: 2
id: finite-c-killing-relation-set-proof
kind: route
title: Turn a failing sequence of finite quotients into one corona homomorphism
target: mf-obstruction-gives-a-finite-c-killing-relation-set
requires:
  - binary-leavitt-all-ranks-full-mf-radical
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

Section 3 of the artifact. Suppose no finite subset of `ker q` works.
Exhaust the countable kernel by finite sets `T_n` and choose finite
groups `Q_n` and homomorphisms `theta_n` with `theta_n(T_n) = 1` and
`theta_n(c) != 1`. Compose each with the left regular representation of
`Q_n` and assemble the sequence in
`prod_n M_(|Q_n|)(C) / {(a_n) : ||a_n|| -> 0}`.

Every fixed word of `ker q` lies in `T_n` for all large `n`, so its
image is eventually the identity and vanishes in the quotient. The
assembled homomorphism therefore factors through `H`. It is nontrivial:
`theta_n(c)` has order three, left translation by it is fixed-point-free,
so its regular unitary has every cube root of unity in its spectrum and
sits at operator distance `sqrt 3` from the identity, which does not
tend to zero.

The image is a subgroup of the unitary group of a norm matrix corona, so
it is MF, and the prerequisite says every homomorphism from the unit
group to an MF group is trivial. That is the contradiction.

The second prerequisite supplies `q` itself, and with it the meaning of
`ker q` and of the 3-cycle generator. The argument is pure compactness
and produces no witness; see the target's own statement on that point.
