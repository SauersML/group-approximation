---
rg: 2
id: reversible-ca-forbids-finite-ground-energy-compilers
kind: claim
title: An explicit reversible automaton forbids every finite-phase conservative compiler preserving the vacuum
distinct_from:
  finite-ground-pattern-energy-forces-surjectivity: that proves surjectivity assuming a nonincreasing local energy with finitely many zero-energy phases; this gives a reversible automaton for which no such energy can exist.
  reversible-xor-has-linear-observable-rank: that computes an observable-rank obstruction for a different reversible rule; this proves unbounded disagreement with every spatial period and excludes all finite-ground local energies and their vacuum-preserving simulation compilers.
artifacts:
  - research/artifacts/finite-ground-energy-and-compiler-obstruction-2026-09-08.md
---

Over Z with alphabet F_2^2, set

    T(a,b)_i=(b_i, a_i+b_i+b_(i+1)).

This fixes the vacuum and is reversible, with inverse

    T^(-1)(c,d)_i=(d_i+c_i+c_(i+1),c_i).

There is no nonnegative finite-range local density e with e(0)=0,
finite simultaneous zero locus, and E(Tx)<=E(x) on every
finite-support input, where E is the sum of its translates.

More precisely, start with a=0 and b a single 1 at the origin. For
every p>=1, the number of sites where T^n x differs from its spatial
p-shift is unbounded in n. Any finite zero-energy subshift has a
common period p. Compactness would bound these disagreements by a
constant times E(T^n x), which nonincrease would keep bounded.

Consequently no finite-alphabet CA with such an energy can simulate T
via an injective local encoding that maps the source vacuum to the
target vacuum and intertwines T with a fixed positive time power of
the target CA. Fixed block packing and spatial shifts are allowed.
A local decoder would imply the required injectivity, but is not
needed for the obstruction. The ambient CA need not be injective.

The conclusion also excludes adding finitely many passive vacuum
tracks or a vacuum-preserving local conjugacy as ways to manufacture
the energy. It does not exclude simulations on a nonzero infinite
background, signed conservation laws, or energies with infinitely
many zero-energy configurations. The displayed T is bijective, so
this is an obstruction to the proposed energy reduction, not a
counterexample to Gottschalk.
