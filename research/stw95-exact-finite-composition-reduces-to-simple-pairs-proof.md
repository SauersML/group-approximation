---
rg: 2
id: stw95-exact-finite-composition-reduces-to-simple-pairs-proof
kind: route
title: Apply the exact filtration reduction successively in both variables
target: stw95-exact-finite-composition-reduces-to-simple-pairs
requires:
  - stw95-exact-finite-ideal-filtration-reduction
---

Every composition factor of an exact algebra is exact.  Fix a composition
factor `Q` of `A`.  Apply the finite-filtration theorem to the composition
series of `B`, tensoring by the exact algebra `Q`; the pairwise hypothesis
shows `Q tensor_min B` is pure.  Now apply the theorem to the composition
series of `A`, tensoring by exact `B`.  All its cell products are pure by the
first step, so `A tensor_min B` is pure.

If `A,B` are pure, Perera--Thiel--Vilalta's extension theorem makes every
ideal and quotient, hence every composition factor, pure.  This gives the
stated reduction to simple exact pure pairs, not a solution of that base case.
