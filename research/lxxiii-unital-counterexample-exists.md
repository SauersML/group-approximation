---
rg: 2
id: lxxiii-unital-counterexample-exists
kind: claim
title: Some unital C-star algebra without finite-dimensional representations has no full square-zero element
distinct_from:
  problem-lxxiii-global-square-zero-cover: that is the positive universal answer to Problem LXXIII; this is a unital counterexample, which would refute it at a=1.
  stw99-problem-lxxiii-global-glimm: that is the STW problem node with its known positive corners; this asserts a specific negative answer in the unital case.
---

**OPEN.**  There is a unital C-star algebra `A` with no nonzero
finite-dimensional representation such that no `x in A` with `x^2=0` is full.

With `a=1` and any `epsilon<1`, `(a-epsilon)_+` is invertible, so such an `A`
refutes `problem-lxxiii-global-square-zero-cover`.  It answers negatively the
unital question of STW's footnote 131, which Elliott and Rordam asked in 2004:
must a unital algebra with no finite-dimensional representations contain a
full square-zero element?  It is a counterexample to the Global Glimm Problem
itself only if `A` is also nowhere scattered, and nothing here assumes that.

Any such `A` must avoid every known positive class: stable rank one
(Antoine--Perera--Robert--Thiel), finite-dimensional Hausdorff primitive ideal
space (Blanchard--Kirchberg), unital real rank zero (Elliott--Rordam), and a
primitive ideal space with a basis of compact open sets (Ng--Thiel--Vilalta).
It must also avoid this graph's own positive classes: a linearly ordered or
laminar ideal lattice, and a properly infinite multiplier host for the unit.

## Attempts

- **Unital homogeneous towers**, route `lxxiii-counterexample-via-homogeneous-tower`.
  By `unital-limit-full-square-zero-at-finite-stage` the obstruction must hold
  at every stage, and by `homogeneous-full-square-zero-is-nilpotent-section`
  it becomes the nonexistence of sections of the bundles of nonzero
  square-zero endomorphisms.  The rational discriminant obstruction proved in
  `full-square-zero-forces-discriminant-power-vanishing` works at any one
  stage, but `discriminant-obstruction-dies-in-multiplicity-towers` shows it
  holds at only finitely many stages of a diagonal tower.  The remaining open
  step is `unital-homogeneous-system-without-full-square-zero`.
