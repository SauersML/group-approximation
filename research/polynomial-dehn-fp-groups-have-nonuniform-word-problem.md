---
rg: 2
id: polynomial-dehn-fp-groups-have-nonuniform-word-problem
kind: claim
title: A computable family of finite presentations with Dehn function n^18 whose uniform word problem is the halting problem
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: that is one finitely presented group with undecidable word problem; here every group in the family has polynomial Dehn function and a word problem decidable in a fixed time bound, and only the uniform problem over the family is undecidable.
  bors-embedding-is-effective-in-the-machine: that is the uniform BORS construction; this applies it to a halting-indexed family of two-generated inputs to produce the non-uniformity.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for individual simple groups beyond every time bound; this family has one time bound for all its members and is not simple.
---

**ESTABLISHED (unreviewed).**  Let `phi_e` be the `e`-th Turing machine.  There
is a computable sequence of finite presentations `P_e`, with groups `H_e`, and
two generators `x_e, y_e` of `P_e`, such that for every `e`:

1. the Dehn function of `P_e` is `<= K_e n^18` for all `n >= 1`;
2. the word problem of `H_e`, on the generators of `P_e`, is decided by a
   deterministic Turing machine in time `<= 2^((n+1)^37)` on every input of
   length `n`;
3. `<x_e, y_e> <= H_e` is the free group `F_2` if `phi_e(0)` does not halt,
   and `Z^2` if it halts; in particular `x_e` has infinite order;
4. `[x_e, y_e] = 1` in `H_e` if and only if `phi_e(0)` halts.

The constant `K_e` and the machine in (2) depend on `e`, and they are not
computable from `e`.  By (4) they cannot be.

**Consequences.**  The word problem is not uniformly solvable from finite
presentations, even over

- the finitely presented groups with Dehn function `<= K n^18` for some `K`, or
- the finitely presented groups whose word problem is decided in time
  `2^((n+1)^37)`, with the time bound exact and not only up to `≼`.

In each class every member has a word problem of fixed, low complexity.  What
is missing is the non-uniform finite information: the halting time of
`phi_e(0)`, which here is a constant in the running time.

DERIVATION
polynomial-dehn-fp-groups-have-nonuniform-word-problem-proof
