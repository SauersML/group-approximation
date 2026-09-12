---
rg: 2
id: thompson-v-one-word-ceiling-from-subquadratic-energy
kind: route
title: Collapse the Bleak--Quick three-cycle from aggregate Carmichael edge energy alone
target: thompson-v-one-word-strict-hs-ceiling
requires:
  - r5-subquadratic-carmichael-energy
  - subquadratic-carmichael-energy-collapse
---

Take the word `w=b=(01 10 11)` and let `U in U(d)^X` be any tuple with
`def_R(U)<=delta_0`.  Put `B=U(b)`.

`r5-subquadratic-carmichael-energy` supplies, for this fixed `U`, an unbounded
sequence of common-pivot packets of unitary conjugates of `B` whose total
squared Carmichael edge energy is `o_U(M^2)`.  Applying
`subquadratic-carmichael-energy-collapse` to `B` inside the fixed dimension
`d` gives

```text
||B-I||_2 <= ||B^3-I||_2.
```

The Bleak--Quick presentation contains `b^3` as a relator, so one fixed
derivation bounds its area by an absolute `C_b` and

```text
||B^3-I||_2 <= C_b def_R(U).
```

Hence `||U(b)-I||_2 <= C_b def_R(U)` for every model.  Choosing
`delta < min(delta_0, 1/(2C_b))` gives `||U(b)-I||_2^2 <= 1/4 <= 2-epsilon`
with `epsilon=7/4`, which is `(TV2)`.  The existing route
`nonhyperlinear-thompson-v-from-one-word-ceiling` then carries this to
non-hyperlinearity of `V` through the binary CE trace face.

This is a different reduction from
`thompson-v-one-word-ceiling-from-r5-carmichael-family`, not a replacement for
it.  By `carmichael-energy-uniform-criteria-incomparable` the two premises are
incomparable: the uniform family bounds every edge but only at the scale
`def_R(U)`, while this route needs no per-edge bound at all but requires the
aggregate energy to be sublinear in the edge count.  Both routes stand, and
neither prerequisite subsumes the other.

The implication in this route remains correct, but its R5 premise is false:
`scalar-phase-refutes-r5-subquadratic-energy` gives arbitrarily accurate
one-dimensional Bleak--Quick tuples for which every conjugate of `U(b)` is the
same scalar and the aggregate energy is exactly quadratic.  Accordingly this
route is recorded only as a conditional implication and is no longer live.

Note also what this route does **not** need.  It uses no Gowers--Hatami
exactification, no representation-dimension bound, no finite-group
multiplication table, and no bound on the length of the conjugating words —
only the order relation `b^3` and an `ell^2` estimate on the pair relators.
