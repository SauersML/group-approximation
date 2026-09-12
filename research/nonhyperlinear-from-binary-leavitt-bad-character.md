---
rg: 2
id: nonhyperlinear-from-binary-leavitt-bad-character
kind: route
title: Use the full Leavitt character simplex to promote a bad character to the canonical trace
target: non-hyperlinear-group
requires:
  - binary-leavitt-full-character-simplex
  - binary-leavitt-nonembeddable-character
artifacts:
  - research/artifacts/leavitt-full-character-classification-2026-09-08.md
---

If `H=L_(F_2)(1,2)^x` were hyperlinear, its canonical trace would have
matrix microstates. The full character classification writes every
character as `a*1+(1-a)*delta_1`; direct sums with identity blocks
then produce microstates for every character. This contradicts the
second prerequisite. Thus that actual bad character would establish
the explicit nonhyperlinear group `H`. The second prerequisite is open.
