# STW Problem XXV: real-rank-zero ordered-K0 audit (2026-08-30)

## Result

For a simple separable unital nuclear non-elementary algebra with unique
trace, stable rank one, and real rank zero,

```text
Z-stability  iff  weak unperforation of K_0.
```

This gives a new structural subclass of Problem XXV and an exact obstruction:
a real-rank-zero counterexample must have perforated ordered `K_0`, and no
other comparison defect survives in that regime.

## Proof audit

There are three separate promotion steps.

1. Every normalized ordered-`K_0` state comes from a quasitrace.  Since the
   algebra is nuclear, quasitraces are traces, so the unique trace is also the
   unique `K_0` state.  Weak unperforation and simplicity give the strict
   state-determined order on `K_0`.  Stable rank one then turns strict trace
   comparison of projection classes into actual subequivalence of
   projections; cancellation is used here and nowhere silently assumed.
2. Real rank zero supplies increasing projection approximate units in
   `Her(a)` and `Her(b)`.  Their trace values increase to the support ranks
   `d_tau(a)` and `d_tau(b)`.  A strict rank gap therefore compares each
   projection under `a` with a projection under `b`; taking the Cuntz
   supremum proves strict comparison for arbitrary positive elements.  No
   uniform spectral-gap or compactness assertion is inserted.
3. The unique trace is a compact zero-dimensional extreme tracial boundary.
   The Toms--White--Winter finite-boundary theorem therefore turns strict
   comparison into Z-stability (equivalently one can factor this through
   unique-trace uniform Gamma and CETW).  Conversely, the Gong--Jiang--Su
   ordered-`K_0` theorem makes every simple unital Z-stable algebra weakly
   unperforated.

## Primary sources

* Bruce Blackadar and Mikael Rordam, *Extending states on preordered
  semigroups and the existence of quasitraces on C-star algebras*, Journal of
  Algebra 152 (1992), 240--247, for surjectivity from quasitraces to ordered
  `K_0` states;
* Marius Dadarlat, *Morphisms of simple tracially AF algebras*, International
  Journal of Mathematics 15 (2004), Proposition 2.8, for the strict
  state-determined order of the real-rank-zero, stable-rank-one, weakly
  unperforated ordered `K_0` group;
* Francesc Perera, *The structure of positive elements for C-star algebras
  with real rank zero*, International Journal of Mathematics 8 (1997),
  383--405, for the projection-semigroup and hereditary-exhaustion comparison
  mechanism in real rank zero and stable rank one;
* Guihua Gong, Xinhui Jiang, and Hongbing Su, *Obstructions to Z-stability
  for unital simple C-star algebras*, Canadian Mathematical Bulletin 43
  (2000), 418--426, for weak unperforation of ordered `K_0` under
  Z-stability;
* Mikael Rordam, *The stable and the real rank of Z-absorbing C-star
  algebras*, International Journal of Mathematics 15 (2004), 1065--1084, for
  almost unperforation under Z-stability;
* Andrew Toms, Stuart White, and Wilhelm Winter, *Z-stability and finite
  dimensional tracial boundaries*, International Mathematics Research
  Notices (2015), for the final strict-comparison-to-Z-stability step; the
  unique trace gives the singleton boundary case.  The equivalent factorized
  route uses the unique-trace central-sequence theorem and the
  Castillejos--Evington--Tikuisis--White uniform-Gamma characterization.

## Boundary

Real rank zero is used decisively: it replaces a soft positive element by an
increasing hereditary projection exhaustion.  Without it, weakly
unperforated `K_0` controls only compact Cuntz classes and cannot see the
trace-invisible soft perforation isolated in the unrestricted XXV frontier.
The theorem therefore does not smuggle in strict comparison, but it also does
not claim that ordered `K_0` controls a general stable-rank-one algebra.
