---
rg: 2
id: kassel-rank-one-braid-closes-central-mark
kind: claim
title: The rank-one braid identity closes the last two centralizer directions of the Kassel long-root mark
artifacts:
  - research/artifacts/kassel-rank-one-braid-closes-central-mark-2026-08-21.md
distinct_from:
  kassel-210-forces-long-weyl-quarter-turn: that centralizes the marked fourth power on three mixed positive-root directions; this closes the opposite long-root pair itself.
  deligne-triple-cover-fd-central-invisibility: that kills the central mark in exact finite-dimensional representations; this proves centrality and quantitative propagation, not exactification.
  maslov-mod3-projective-defect-gap: that asks for a positive approximate-relator floor; centrality is automatic in the scalar sector and does not imply that floor.
---

Kassel Lemma 2.2 is equivalent, for the opposite long-root generators, to

```text
b B^(-1)b=B^(-1)b B^(-1).
```

This braid identity makes `w=bB^(-1)b` exchange `b` and `B^(-1)` by
conjugation. Hence `w^2`, and therefore `z=w^4`, centralizes both `b` and
`B`. If the braid defect is `epsilon` in normalized HS norm, the commutator
defects of `w^4` with either generator are at most `4epsilon`.

Together with the mixed quarter-turn identities and their negative-root
symmetries, this makes `z` central on the full root presentation. It does not
turn Deligne exact finite-dimensional invisibility into an approximate gap.

