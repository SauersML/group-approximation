# Dyadic Iwahori random-lift audit — 2026-08-21

## Exact outcome

The most literal construction—take many copies of the index-three
`Gamma_0(2)` sheets and randomly match them across the two modular
vertices—cannot work.  On the first three-sheet action the abstract
parabolic `T` is a transposition; on the second it is represented by
`T'^2`, hence is the identity.  The edge defect is therefore exactly `2/3`
for every number of unamplified copies and every matching.

This is a local obstruction, not a proof of nonsoficity.  Long internal
cycles can make square-root cycle data asymptotically flexible.  The audit
therefore isolates the next finite target rather than extrapolating the
`2/3` bound beyond its scope.

## Amplified finite target

Write

```text
A=C_0 *_B C_1,
C_j=C_2*C_3,
B=<T,w> ~= Z*C_2.
```

A successful construction may be searched for entirely in finite
permutations:

1. choose exact finite actions of both `C_j` on one amplified set;
2. make the two `B` generator actions asymptotically agree;
3. require that alternating amalgam normal forms send almost every point
   into distinct `C_0`-orbit blocks on every fixed radius.

Condition 3 is the collision condition that a random-centralizer argument
must prove.  It is stronger than matching the individual relative
permutation characters: character matching controls fixed-point statistics,
whereas orbit charts require simultaneous separation of every pair in a
finite coset window.

The two exact vertex actions are required on the same finite set.  Agreement
of the two edge generators in normalized Hamming distance then supplies one
common approximate action of the amalgam: every fixed normal-form equality
uses only finitely many edge substitutions, so its failure set has vanishing
density by a union bound.  There is no passage from unrelated local models
at this step.

The route `dyadic-random-lifts-produce-sofic-vertex-action` proves that
these three finite properties suffice for soficity of the Bruhat--Tits
vertex action.  Thus the unresolved sign has been reduced to a concrete
amplified common-edge coupling problem.  The raw three-sheet ansatz is
rigorously eliminated.

## Dependency impact

A positive construction establishes
`dyadic-bruhat-tits-vertex-action-is-sofic`, hence activates the already
proved consequences:

```text
flexible permutation instability of PSL_2(Z[1/2]);
soficity of the full centralizer HNN/free-coset-wreath witness;
finite-coordinate countermodels to canonical Iwahori commutant transfer.
```

It would therefore refute, rather than prove, the proposed stability route
to nonhyperlinearity.  A proof that no amplified coupling exists would need
a genuinely amplification-stable invariant; the three-sheet support count
is not one.
