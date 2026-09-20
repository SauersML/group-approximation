---
rg: 2
id: lifted-thompson-t-not-mf-via-chromatic-code
kind: route
title: A bounded-area commutator code with a non-central mark, plus the radical dichotomy, kills the centre of T-bar
target: lifted-thompson-t-is-not-mf
requires:
  - lifted-thompson-t-bounded-area-chromatic-code
  - infinite-chromatic-commutator-code-kills-mf-mark
  - lifted-thompson-t-mf-radical-dichotomy
---

**Why this route.**  `lifted-thompson-t-is-not-mf` alone gives both deep inputs
of `property-t-free-manuscript-results`.  Its previous route
`lifted-thompson-t-not-mf-via-central-eigencorners` has two open leaves:

- `thompson-t-has-full-mf-radical`;
- `lifted-thompson-t-centre-has-commutant-eigencorners`, whose torus-knot
  route is refuted by `torus-knot-k34-expander-pair-has-no-eigencorner`.  Any
  proof of it must now use the Thompson relators.

This route has one open leaf, which is combinatorial (a uniform van Kampen
area bound) and presentation-independent.  No Property `(T)`, Kazhdan
projection or stability input appears.

## Steps

1. **Code.**  By `lifted-thompson-t-bounded-area-chromatic-code`, `T̄` has a
   bounded-area infinite-chromatic commutator code with some mark `x != 1`
   in `T̄`.
2. **Kill the mark.**  By `infinite-chromatic-commutator-code-kills-mf-mark`,
   `x in Rad_MF(T̄)`.
3. **Full radical.**  So `Rad_MF(T̄) != 1`, and by
   `lifted-thompson-t-mf-radical-dichotomy`, `Rad_MF(T̄) = T̄`.  In particular
   `z in Rad_MF(T̄)`, which is the target.

## Why the mark is not `z`

The obvious design marks `z` itself.  It is impossible:

- `central-marks-escape-chromatic-codes` proves that no commutator of `T̄` is
  a nontrivial power of `z`, via the translation number, so CCC1 dies;
- the same node proves that conjugacy-difference codes never mark a central
  element, in any group, so CDC2 dies.

The dichotomy is what makes a non-central mark sufficient.  An exact skeleton
with a non-central mark is `lifted-thompson-t-exact-wandering-commutator-table`.
